#!/usr/bin/env python3
"""Run with `lake env python3 Tests/BlueprintVerify/report_regression.py` after building.
Checks `#verify_blueprint ... (report := ...)` for every verdict, including aborted runs,
against verification-report.schema.json. Mutated documents live in a temporary directory.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import os

from jsonschema import Draft202012Validator
from runtime import lean_command
lean_args = lean_command()

repo = Path(os.environ.get('PLUTUS_CORE_REPO', Path(__file__).resolve().parents[2]))
schema = Draft202012Validator(json.loads(
    (repo / 'PlutusCore/UPLC/BlueprintEncoding/verification-report.schema.json').read_text()))
placeholder = json.loads((repo / 'Tests/BlueprintVerify/fixtures/assurance.json').read_text())
placeholder['blueprint']['uri'] = str((repo / 'Tests/test/plutus.json').resolve())
placeholder.pop('formalFragments', None)
base = placeholder['properties'][0]
base.pop('evidence', None)
game = json.loads((repo / 'Tests/BlueprintVerify/Game/assurance.json').read_text())
game['blueprint']['uri'] = str((repo / 'Tests/BlueprintVerify/Game/plutus.json').resolve())

def prop(id, source=None, formal=True):
    p = copy.deepcopy(base); p['id'] = id
    if not formal: p['statement'].pop('formal')
    elif source is not None: p['statement']['formal']['source'] = source
    return p

def sha256(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify(root, doc, report=True):
    path = root / 'assurance.json'
    path.write_text(doc if isinstance(doc, str) else json.dumps(doc))
    option = f' (report := {json.dumps(str(root / "report.json"))})' if report else ''
    driver = root / 'Check.lean'
    driver.write_text('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'
                      f'#verify_blueprint Check {json.dumps(str(path))}{option}\n')
    proc = subprocess.run(lean_args + [str(driver)], cwd=repo, text=True, capture_output=True, timeout=300)
    return proc.returncode, proc.stdout + proc.stderr

def run_case(name, doc, status, expected, code=None):
    """`expected` lists (verdict, reason substring or None) per property, in order."""
    with tempfile.TemporaryDirectory(prefix='report-') as td:
        root = Path(td)
        exit_code, log = verify(root, doc)
        try:
            report = json.loads((root / 'report.json').read_text())
            schema.validate(report)
            assert report['status'] == status, report['status']
            assert (exit_code == 0) == (status == 'passed'), exit_code
            got = [(p['verdict'], p['reason']) for p in report['properties']]
            assert len(got) == len(expected), got
            for (verdict, reason), (want, fragment) in zip(got, expected):
                assert verdict == want and (fragment is None or fragment in (reason or '')), got
            assert report['assurance']['hash']['digest'] == sha256(root / 'assurance.json')
            if code: code(report, log)
        except AssertionError as e:
            raise AssertionError(f'{name}: {e}\n{log}') from e
        print(f'PASS {name}', flush=True)

src = base['statement']['formal']['source']
def summary(checked, not_checked, failed):
    def check(report, log):
        assert report['summary'] == {'checked':checked, 'notChecked':not_checked, 'failedOrInconclusive':failed}, report['summary']
        if report['status'] != 'error':
            assert f'{checked} checked, {not_checked} not checked, {failed} failed/inconclusive' in log
    return check

def verified(report, log):
    summary(1, 1, 0)(report, log)
    assert report['blueprint']['hash']['digest'] == sha256(placeholder['blueprint']['uri'])
    assert report['trust'] == {'method':'smt', 'tool':'Blaster', 'reconstructedLeanProof':False}
    assert report['properties'][0]['scope'] == {'validators':base['scope']['validators'], 'functions':[]}
run_case('verified and not checked', dict(placeholder, properties=[prop('fresh'), prop('prose', formal=False)]),
         'passed', [('verified', None), ('not_checked', 'natural-language only')], verified)

falsified = copy.deepcopy(game)
falsified['properties'] = falsified['properties'][:1]
formal = falsified['properties'][0]['statement']['formal']
formal['source'] = formal['source'].replace('isSuccessful', 'isUnsuccessful')
def counterexample(report, log):
    summary(1, 0, 1)(report, log)
    assert isinstance(report['properties'][0]['counterexample'], list)
run_case('falsified', falsified, 'failed', [('falsified', None)], counterexample)

# A valid claim conjoined with one the solver cannot decide within its timeout.
run_case('inconclusive', dict(placeholder, properties=[prop('undecided',
         f'({src}) ∧ (∀ (x : Int), ∃ (y : Int), x < y * y)')]),
         'failed', [('inconclusive', 'undetermined')], summary(1, 0, 1))

# Elaboration failure aborts the command mid-loop: earlier verdicts survive and
# later properties are explicitly not reached.
run_case('aborted during checking', dict(placeholder, properties=[
    prop('fresh'), prop('broken', '∀ (d : Data), notDefinedAnywhere d'), prop('later'), prop('prose', formal=False)]),
    'error', [('verified', None), ('error', 'formal proposition contains sorry'),
              ('not_checked', 'not reached'), ('not_checked', 'not reached')], summary(1, 0, 0))
def bad_blueprint_hash(d):
    d = copy.deepcopy(d); d['blueprint']['hash']['digest'] = '00'*32; return d
def unreached(report, log):
    summary(0, 0, 0)(report, log)
    assert 'Blueprint hash mismatch' in report['error']
    assert report['blueprint']['hash']['digest'] == sha256(placeholder['blueprint']['uri'])
run_case('aborted before checking', bad_blueprint_hash(dict(placeholder, properties=[prop('fresh')])),
         'error', [('not_checked', 'not reached')], unreached)
run_case('invalid document', '{', 'error', [],
         lambda report, log: report['error'].startswith('Invalid assurance document'))

# Without the option nothing is written and the log is byte-for-byte unchanged.
with tempfile.TemporaryDirectory(prefix='report-') as td:
    root = Path(td)
    doc = dict(placeholder, properties=[prop('fresh'), prop('prose', formal=False)])
    plain = verify(root, doc, report=False)
    assert not (root / 'report.json').exists(), 'report written without the option'
    reported = verify(root, doc)
    assert plain == reported, f'log changed by the report option\n{plain}\n{reported}'
    print('PASS log and exit code unchanged by the report option', flush=True)
print('All verification report cases passed.')
