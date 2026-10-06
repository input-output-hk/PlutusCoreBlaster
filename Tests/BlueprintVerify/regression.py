#!/usr/bin/env python3
"""Run with `lake env python3 Tests/BlueprintVerify/regression.py` after building.
The fixtures are read-only; mutated documents live in a temporary directory.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import os
import sys

from runtime import lean_command
lean_args = lean_command()

repo = Path(os.environ.get('PLUTUS_CORE_REPO', Path(__file__).resolve().parents[2]))
fixture = json.loads((repo / 'Tests/BlueprintVerify/fixtures/assurance.json').read_text())
blueprint = (repo / 'Tests/test/plutus.json').resolve()
fixture['blueprint']['uri'] = str(blueprint)
fixture['properties'] = fixture['properties'][:1]
fixture['properties'][0].pop('evidence', None)
fixture.pop('formalFragments', None)
lean = os.environ.get('LEAN', 'lean')

def run_case(name, modify, expected=None):
    with tempfile.TemporaryDirectory(prefix='assurance-') as td:
        root = Path(td)
        doc = copy.deepcopy(fixture)
        modify(doc, root)
        path = root/'assurance.json'
        path.write_text(json.dumps(doc))
        driver = root/'Check.lean'
        driver.write_text('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'
                          f'#verify_blueprint Check {json.dumps(str(path))}\n')
        proc = subprocess.run(lean_args + [str(driver)], cwd=repo, text=True, capture_output=True, timeout=120)
        output = proc.stdout + proc.stderr
        good = (proc.returncode == 0 and 'verified (Blaster SMT' in output) if expected is None else (proc.returncode != 0 and expected.lower() in output.lower())
        if expected is not None and ': verified (Blaster SMT' in output:
            good = False
        if not good:
            raise AssertionError(f'{name}: exit {proc.returncode}\n{output}')
        print(f'PASS {name}', flush=True)

run_case('fresh property', lambda d, p: None)
def incomplete_smt_evidence(d,p):
    d['properties'][0]['evidence'] = [{'method':'smt-check','verifier':'test','tool':'blaster',
                                     'outcome':'verified','date':'2026-09-29','scriptHash':'00'*28}]
run_case('SMT evidence requires an artifact', incomplete_smt_evidence, "missing 'artifact'")
run_case('unknown schema', lambda d,p: d.update({'$schema':'https://invalid/schema'}), 'unsupported schema identifier')
run_case('missing authors', lambda d,p: d['preamble'].pop('authors'), "missing 'authors'")
run_case('duplicate property id', lambda d,p: d['properties'].append(copy.deepcopy(d['properties'][0])), 'duplicate property')
run_case('unknown language', lambda d,p: d['languages'].clear(), 'unknown language')
run_case('unknown validator', lambda d,p: d['properties'][0]['scope'].update(validators=['absent']), 'no validator')
run_case('disconnected proposition', lambda d,p: d['properties'][0]['statement']['formal'].update(source='True'), 'does not depend')
run_case('invalid blueprint digest', lambda d,p: d['blueprint']['hash'].update(digest='00'*32), 'Blueprint hash mismatch')
run_case('unsupported digest', lambda d,p: d['blueprint']['hash'].update(alg='unknown'), 'Unsupported blueprint digest')

def script_mismatch(d,p):
    bp = json.loads(blueprint.read_text())
    bp['validators'][0]['hash'] = '00'*28
    target = p/'plutus.json'; target.write_text(json.dumps(bp))
    d['blueprint'] = {'uri':str(target), 'hash':{'alg':'sha256','digest':hashlib.sha256(target.read_bytes()).hexdigest()}}
run_case('inconsistent script bytes and hash', script_mismatch, 'compiledCode hash mismatch')

def cycle(d,p):
    d['formalFragments'] = [{'id':'unused','language':'lean','imports':['unused'],'source':'def a := True'}]
run_case('unused fragment cycle', cycle, 'cycle')

def axiom(d,p):
    d['formalFragments'] = [{'id':'bad','language':'lean','source':'axiom bad : False'}]
    d['properties'][0]['statement']['formal']['uses'] = ['bad']
run_case('fragment axioms', axiom, 'only def/abbrev')

def exhaust(d,p):
    d['properties'][0]['statement']['formal']['source'] = d['properties'][0]['statement']['formal']['source'].replace('2500','0')
run_case('fuel exhaustion is not rejection', exhaust, 'falsified')

for outcome in ['inconclusive', 'partial', 'falsified']:
    def old_evidence(d,p,outcome=outcome):
        ev = copy.deepcopy(json.loads((repo/'Tests/BlueprintVerify/fixtures/assurance.json').read_text())['properties'][0]['evidence'][0])
        ev['outcome'] = outcome
        d['properties'][0]['evidence'] = [ev]
    run_case('fresh check after '+outcome, old_evidence)
def local_artifact(d,p,tampered=False):
    target = p/'binary artifact.bin'; target.write_bytes(bytes(range(256)))
    evidence = copy.deepcopy(json.loads((repo/'Tests/BlueprintVerify/fixtures/assurance.json').read_text())['properties'][0]['evidence'][0])
    evidence['method'] = 'smt-check'
    evidence['artifact'] = {'uri':str(target),'hash':{'alg':'sha256','digest':('00'*32 if tampered else hashlib.sha256(target.read_bytes()).hexdigest())}}
    d['properties'][0]['evidence'] = [evidence]
run_case('local binary artifact digest', local_artifact)
run_case('tampered local artifact', lambda d,p: local_artifact(d,p,True), 'artifact digest mismatch')

# Exercise the 0.5 profile against a real compiled nontrivial script.
fixture = json.loads((repo/'Tests/BlueprintVerify/Game/assurance.json').read_text())
blueprint = (repo/'Tests/BlueprintVerify/Game/plutus.json').resolve()
fixture['blueprint']['uri'] = str(blueprint)
fixture['properties'] = fixture['properties'][:1]
run_case('generated UAL 0.5 game', lambda d,p: None)
run_case('missing fragment reference', lambda d,p: d['properties'][0]['statement']['formal'].update(uses=['absent']), 'no formal fragment')
run_case('falsified compiled game claim', lambda d,p: d['properties'][0]['statement']['formal'].update(source=d['properties'][0]['statement']['formal']['source'].replace('isSuccessful', 'isUnsuccessful')), 'falsified')

def mutate_blueprint(d,p,mutate):
    bp = json.loads(blueprint.read_text())
    mutate(bp['validators'][0])
    target = p/'plutus.json'; target.write_text(json.dumps(bp))
    d['blueprint'] = {'uri':str(target), 'hash':{'alg':'sha256','digest':hashlib.sha256(target.read_bytes()).hexdigest()}}
run_case('missing argument schema', lambda d,p: mutate_blueprint(d,p,lambda v: v['arguments'][0].pop('schema')), 'missing schema')
run_case('unresolved argument schema', lambda d,p: mutate_blueprint(d,p,lambda v: v['arguments'][0].update(schema={'$ref':'#/definitions/Absent'})), 'unresolved argument schema')
run_case('missing explicit semantics', lambda d,p: mutate_blueprint(d,p,lambda v: v['budget'].pop('semantics')), 'explicit steps budget')
run_case('unknown UAL version', lambda d,p: d['languages']['ual'].update(version='4'), 'unsupported formal-language version')
def bad_fragment_version(d,p):
    d['languages']['future'] = {'name':'Lean','version':'999'}
    d['formalFragments'][0]['language'] = 'future'
run_case('unsupported fragment version', bad_fragment_version, 'unsupported fragment language version')
run_case('unsupported argument type', lambda d,p: mutate_blueprint(d,p,lambda v: v['arguments'][0].update(schema={'dataType':'unsupported'})), 'unsupported argument datatype')
print('All assurance regression cases passed.')
