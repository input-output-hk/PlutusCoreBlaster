#!/usr/bin/env python3
"""Generate and verify recursive Data contracts. Run under lake env."""
import copy
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from runtime import lean_command

repo = Path(__file__).resolve().parents[2]
generator, out = (Path(x).resolve() for x in sys.argv[1:3])
out.mkdir(parents=True, exist_ok=True)
for name in ['run-report.json', 'verified-assurance.json']:
    (out / name).unlink(missing_ok=True)
lean_args = lean_command()
header = 'import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'
def write(path, value): path.write_text(json.dumps(value, indent=2) + '\n')
def digest(path): return {'alg':'sha256', 'digest':hashlib.sha256(path.read_bytes()).hexdigest()}
def run(name, source):
    path = out / (name + '.lean'); path.write_text(header + source)
    p = subprocess.run(lean_args + [str(path)], cwd=repo, text=True, capture_output=True, timeout=600)
    log = p.stdout + p.stderr; (out / (name + '.log')).write_text(log)
    return p.returncode, log
code, log = run('Environment', f'#write_checking_environment {json.dumps(str(out / "environment.json"))}\n')
if code: raise RuntimeError(log)
subprocess.run([str(generator), 'environment.json'], cwd=out, check=True)
doc = json.loads((out / 'assurance.json').read_text())
bp = json.loads((out / 'plutus.json').read_text())
assert set(doc['functions']) == {'mirrorData'} and 'functions' not in bp
assert [v['id'] for v in bp['validators']] == ['treeValidator']
ref = doc['functions']['mirrorData']['arguments'][0]['$ref']
key = ref.removeprefix('#/definitions/').replace('~1','/').replace('~0','~')
assert ref in json.dumps(doc['definitions'][key]), 'generator lost the recursive reference'
expected = {'leaf_seven','nested_sum','nested_mirror','malformed_tree'}
def check(prop):
    d = copy.deepcopy(doc); d['properties'] = [prop]
    path = out / (prop['id'] + '.json'); write(path, d)
    code, log = run(prop['id'], f'#verify_blueprint Recursive {json.dumps(str(path))}\n')
    print(log, end='', flush=True)
    if code or set(re.findall(r"Property '([^']+)': verified",log)) != {prop['id']}: raise RuntimeError(prop['id'])
with ThreadPoolExecutor(max_workers=3) as pool: list(pool.map(check, doc['properties']))
assert {p['id'] for p in doc['properties']} == expected

# Exact same recursive schema reaches both a parameter and a helper Data boundary.
# The concrete witness rules out an empty/success-impossible specification domain.
code, log = run('Witness', f'''#import_blueprints Witness {json.dumps(str(out / 'plutus.json'))}
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine PlutusCore.Data
#eval show IO Unit from do
  let good := Data.Constr 1 [Data.Constr 0 [Data.I 2], Data.Constr 1 [Data.Constr 0 [Data.I 1], Data.Constr 0 [Data.I 4]]]
  let result := cekExecuteProgramWithSemanticVariant .defaultFunSemanticsVariantE Witness.Tree_validator.script [.Const (.Data good), .Const (.Data (.I 0))] 3000
  match result with
  | .Halt (.VCon .Unit) => IO.println "PASS inhabited recursive tree accepted"
  | _ => throw (IO.userError "recursive witness failed")
''')
if code: raise RuntimeError(log)
print(log, end='', flush=True)
helper = copy.deepcopy(doc)
helper['properties'] = [p for p in helper['properties'] if p['id']=='nested_mirror']
negatives = []
def reject(name, change, expected):
    d=copy.deepcopy(helper);change(d);path=out/(name+'.json');write(path,d)
    code,log=run(name,f'#verify_blueprint Negative {json.dumps(str(path))}\n')
    if code==0 or expected not in log: raise AssertionError(name+'\n'+log)
    negatives.append(name);print('PASS',name,flush=True)
reject('stale-definitions',lambda d:d['definitions'][key].update(title='changed'), 'checking function definitions mismatch')
reject('alias-cycle',lambda d:d['definitions'].__setitem__(key,{'$ref':ref}), 'unguarded recursive schema')
reject('missing-definition',lambda d:d['definitions'].pop(key), 'unresolved argument schema')
reject('false-mirror',lambda d:d['properties'][0]['statement']['formal'].update(source='∀ (n : Integer), mirrorData_returns (leaf n) (leaf (n + 1))'), 'falsified')
report={'status':'verified','properties':sorted(expected),'negativeChecks':negatives,'concreteWitness':'Branch (Leaf 2) (Branch (Leaf 1) (Leaf 4)) accepted',
        'generatorHash':digest(generator),'blueprintHash':digest(out/'plutus.json'),'assuranceHash':digest(out/'assurance.json'),
        'scope':'Symbolic integers at fixed recursive tree shapes under 3000 CEK steps; not arbitrary-depth termination.',
        'trust':'Blaster SMT; no reconstructed Lean kernel proof.'}
write(out/'run-report.json',report)
evidence_doc=copy.deepcopy(doc);evidence_doc['tools']={'blaster':{'name':'Blaster','version':'loaded-environment'}}
for prop in evidence_doc['properties']:
    ev={'method':'smt-check','verifier':'Blaster','tool':'blaster','outcome':'verified','date':datetime.now(timezone.utc).date().isoformat(),
        'checkingContextHash':doc['checkingContexts'][prop['checkingContext']]['hash'],'artifact':{'uri':'run-report.json','hash':digest(out/'run-report.json')},'notes':report['scope']+' '+report['trust']}
    if prop['scope'].get('validators'):ev['scriptHash']=bp['validators'][0]['hash']
    if prop['scope'].get('functions'):ev['functionHashes']={'mirrorData':doc['functions']['mirrorData']['hash']}
    prop['evidence']=[ev]
write(out/'verified-assurance.json',evidence_doc)
print('PASS recursive end-to-end verification',flush=True)
