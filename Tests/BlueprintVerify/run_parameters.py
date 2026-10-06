#!/usr/bin/env python3
"""Verify freshly compiled Data/native parameter examples and reject swapped wire types.
Usage: lake env python3 Tests/BlueprintVerify/run_parameters.py GENERATOR OUTPUT
"""
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from runtime import lean_command
lean_args = lean_command()

repo=Path(__file__).resolve().parents[2]
generator=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=True)
def run(source,name):
    path=out/name;path.write_text(source)
    result=subprocess.run(lean_args + [str(path)],cwd=repo,text=True,capture_output=True,timeout=300)
    log=result.stdout+result.stderr;(out/(name+'.log')).write_text(log)
    return result.returncode,log
code,log=run('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'+f'#write_checking_environment {json.dumps(str(out/"environment.json"))}\n','Environment.lean')
if code: raise RuntimeError(log)
subprocess.run([str(generator),'environment.json'],cwd=out,check=True,timeout=120)
code,log=run('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'+f'#verify_blueprint Parameters {json.dumps(str(out/"assurance.json"))}\n','Check.lean')
print(log,end='')
if code or set(re.findall(r"Property '([^']+)': verified",log)) != {'native_seven','data_seven','native_applied_seven','native_applied_eight','data_applied_seven','data_applied_eight'}:
    raise RuntimeError('parameter verification did not verify all six claims')
# Keep the exact compiled program, change only its declared parameter wire type.
# This must produce a false proposition, demonstrating that encodings affect execution.
bp=json.loads((out/'plutus.json').read_text());doc=json.loads((out/'assurance.json').read_text())
for v in bp['validators']:
    if v['id']=='nativeParameter': v['parameters'][0]['schema']={'dataType':'integer'}
(out/'wrong-wire.json').write_text(json.dumps(bp))
doc['blueprint']={'uri':'wrong-wire.json','hash':{'alg':'sha256','digest':hashlib.sha256((out/'wrong-wire.json').read_bytes()).hexdigest()}}
doc['properties']=[p for p in doc['properties'] if p['id']=='native_seven']
(out/'wrong-wire-assurance.json').write_text(json.dumps(doc))
code,log=run('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'+f'#verify_blueprint Wrong {json.dumps(str(out/"wrong-wire-assurance.json"))}\n','WrongWire.lean')
if code == 0 or "Property 'native_seven': falsified" not in log: raise RuntimeError(log)
print('PASS swapped native/Data schema falsifies the claim over the same compiled bytes')

# Mutate fresh applied contexts independently and rebind metadata when the test
# concerns semantic identity rather than stale artifact bytes.
original=json.loads((out/'assurance.json').read_text())
base_prop=next(p for p in original['properties'] if p['id']=='native_applied_seven')
base_context=json.loads((out/original['checkingContexts'][base_prop['checkingContext']]['uri']).read_text())
def h(path): return {'alg':'sha256','digest':hashlib.sha256(path.read_bytes()).hexdigest()}
def write(path, obj): path.write_text(json.dumps(obj,indent=2)+'\n')
def reject(name, change, expected):
    d=copy.deepcopy(original);d['properties']=[copy.deepcopy(base_prop)]
    c=copy.deepcopy(base_context);change(c,d)
    cp=out/(name+'-context.json');write(cp,c)
    d['checkingContexts'][base_prop['checkingContext']]={'uri':cp.name,'hash':h(cp)}
    ap=out/(name+'-assurance.json');write(ap,d)
    code,log=run('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'+f'#verify_blueprint AppliedNegative {json.dumps(str(ap))}\n',name+'.lean')
    if code==0 or expected not in log or ': verified (Blaster SMT' in log: raise AssertionError(name+'\n'+log)
    print('PASS',name,flush=True)
def params(c): return c['targets'][0]['parameters']
reject('applied-wrong-order',lambda c,d:params(c)['values'][0].update(parameter='/parameters/1'),'applied parameter order/reference mismatch')
reject('applied-missing-script',lambda c,d:params(c).pop('appliedScript'),'expected exactly one schema alternative')
reject('applied-wrong-hash',lambda c,d:params(c).update(appliedScriptHash='00'*28),'applied script hash mismatch')
reject('applied-extra-value',lambda c,d:params(c)['values'].append(copy.deepcopy(params(c)['values'][0])),'must cover every parameter')
other=json.loads((out/'checking-native_applied_eight.json').read_text())['targets'][0]['parameters']
reject('applied-unrelated-script',lambda c,d:params(c).update(appliedScript=other['appliedScript'],appliedScriptHash=other['appliedScriptHash']),'not the ordered application')
data_context=json.loads((out/'checking-data_applied_seven.json').read_text())['targets'][0]['parameters']
reject('applied-wrong-wire',lambda c,d:params(c)['values'][0].update(term=data_context['values'][0]['term']),'does not match its value schema')
def bad_term(c,d,payload,rebind=True):
    path=out/'bad-parameter.flat';path.write_bytes(payload)
    params(c)['values'][0]['term']={'uri':path.name,'hash':h(path) if rebind else {'alg':'sha256','digest':'00'*32}}
reject('applied-stale-term',lambda c,d:bad_term(c,d,b'bad',False),'checking artifact digest mismatch')
valid=(out/params(base_context)['values'][0]['term']['uri']).read_bytes()
reject('applied-trailing-term',lambda c,d:bad_term(c,d,valid+b'\x00'),'trailing or invalid Flat parameter padding')
reject('applied-open-term',lambda c,d:bad_term(c,d,bytes.fromhex('200201')),'invalid or open Flat parameter term')
print('PASS six parameter claims and nine applied-binding negative checks',flush=True)
