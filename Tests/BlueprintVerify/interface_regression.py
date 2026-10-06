#!/usr/bin/env python3
"""Negative checks over a freshly generated UAL 0.6-draft bundle.
Usage: lake env python3 Tests/BlueprintVerify/interface_regression.py /path/to/run
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

source = Path(sys.argv[1]).resolve()
from runtime import lean_command
lean_args = lean_command()

repo = Path(os.environ.get('PLUTUS_CORE_REPO', Path(__file__).resolve().parents[2]))
lean = os.environ.get('LEAN', 'lean')
def h(path): return {'alg':'sha256','digest':hashlib.sha256(path.read_bytes()).hexdigest()}
def write(path, obj): path.write_text(json.dumps(obj,indent=2)+'\n')

def run(name, change, expected, rebind=True):
    with tempfile.TemporaryDirectory(prefix='interface-') as td:
        root=Path(td)
        for path in source.glob('*.json'):
            if path.name not in ['run-report.json','verified-assurance.json']:
                (root/path.name).write_bytes(path.read_bytes())
        doc=json.loads((root/'assurance.json').read_text())
        doc['properties']=doc['properties'][:1]
        bp=json.loads((root/'plutus.json').read_text())
        key=doc['properties'][0]['checkingContext']
        context_path=root/doc['checkingContexts'][key]['uri']
        ctx=json.loads(context_path.read_text())
        change(doc,bp,ctx,root)
        write(root/'plutus.json',bp)
        doc['blueprint']['hash']=h(root/'plutus.json')
        write(context_path,ctx)
        if rebind: doc['checkingContexts'][key]['hash']=h(context_path)
        write(root/'assurance.json',doc)
        (root/'Check.lean').write_text('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'
            f'#verify_blueprint Check {json.dumps(str(root/"assurance.json"))}\n')
        p=subprocess.run(lean_args + [str(root/'Check.lean')],cwd=repo,text=True,capture_output=True,timeout=300)
        log=p.stdout+p.stderr
        if p.returncode == 0 or expected.lower() not in log.lower():
            raise AssertionError(f'{name}: expected rejection containing {expected!r}, exit={p.returncode}\n{log}')
        print('PASS',name,flush=True)

def nothing(d,b,c,r): pass
run('altered context bytes',nothing,'checking artifact digest mismatch',False)
run('missing context',lambda d,b,c,r:d['properties'][0].pop('checkingContext'),'requires a checkingContext')
run('unknown context',lambda d,b,c,r:d['properties'][0].update(checkingContext='missing'),'unknown checking context')
run('unsupported profile',lambda d,b,c,r:c.update(profile='unknown'),'unsupported checking profile')
run('incomplete target coverage',lambda d,b,c,r:c['targets'][0].update(validator='elsewhere'),'exactly cover')
run('duplicate targets',lambda d,b,c,r:c['targets'].append(copy.deepcopy(c['targets'][0])),'duplicate checking target')
run('unknown invocation',lambda d,b,c,r:c['targets'][0].update(purpose='mint'),'unknown invocation')
run('applied parameters',lambda d,b,c,r:c['targets'][0].update(parameters={'mode':'applied','values':[{'parameter':'/parameters/0','term':{'uri':'unused.flat','hash':{'alg':'sha256','digest':'00'*32}}}],'appliedScriptHash':'00'*28}),'expected exactly one schema alternative')
run('missing semantics',lambda d,b,c,r:c['execution'].pop('semanticsVariant'),"missing 'semanticsVariant'")
run('step exhaustion is not success',lambda d,b,c,r:c['execution']['budget'].update(steps=0),'falsified')
run('falsified claim',lambda d,b,c,r:d['properties'][0]['statement']['formal'].update(source='∀ (actual guess : ByteString) (ctx : Data), hashMatches actual guess → isUnsuccessful (gameValidator (Data.B actual) (Data.B guess) ctx)'),'falsified')
run('step budget cannot claim ledger acceptance',lambda d,b,c,r:c['execution'].update(acceptance='ledger-script'),"missing 'protocolVersion'")
def env_changed(d,b,c,r):
    p=r/c['environment']['uri'];obj=json.loads(p.read_text());obj['solverSha256']='00'*32;write(p,obj);c['environment']['hash']=h(p)
run('environment content differs from running checker',env_changed,'checking environment does not match')
run('unbound environment bytes',lambda d,b,c,r:(r/c['environment']['uri']).write_text('{}'),'checking artifact digest mismatch')
run('legacy budget in new dialect',lambda d,b,c,r:b['validators'][0].update(budget={'steps':500,'semantics':'D'}),'forbidden combination')
run('wrong language convention',lambda d,b,c,r:b['validators'][0]['interface'].update(callingConvention='ledger-v3'),'does not match Plutus')
run('incomplete invocation',lambda d,b,c,r:b['validators'][0]['interface']['invocations'][0]['arguments'].pop(),'incomplete invocation')
run('runtime order',lambda d,b,c,r:b['validators'][0]['interface']['invocations'][0]['arguments'].reverse(),'invalid runtime argument order')
run('native runtime',lambda d,b,c,r:b['validators'][0]['datum'].update(schema={'dataType':'#integer'}),'runtime payload must be Data')
run('unknown dialect',lambda d,b,c,r:b.update({'$schema':'unknown'}),'unsupported blueprint dialect')
run('missing vocabulary',lambda d,b,c,r:b.pop('$vocabulary'),"missing '$vocabulary'")
run('altered code hash',lambda d,b,c,r:b['validators'][0].update(hash='00'*28),'compiledCode hash mismatch')

def parameter(schema):
    def change(d,b,c,r):
        v=b['validators'][0]
        v['parameters']=[{'schema':schema}]
        v['interface']['invocations'][0]['arguments'].insert(0,{'role':'parameter','source':'/parameters/0'})
    return change
run('Scott is explicit unsupported',parameter({'dataType':'#scott','encoding':'unknown','constructors':[{'name':'One','fields':[]}]}),'Scott encoding is not supported')
run('native in a Data container',parameter({'dataType':'list','items':{'dataType':'#integer'}}),'native values cannot occur inside Data')
run('recursive parameter',lambda d,b,c,r:(b.setdefault('definitions',{}).update(Loop={'$ref':'#/definitions/Loop'}),parameter({'$ref':'#/definitions/Loop'})(d,b,c,r)),'recursive schema encoding')
def evidence_missing(d,b,c,r):
    d['properties'][0]['evidence']=[{'method':'smt-check','verifier':'test','tool':'blaster','outcome':'verified','date':'2026-09-30','scriptHash':b['validators'][0]['hash'],'artifact':{'uri':'environment.json','hash':h(r/'environment.json')}}]
    d['tools']={'blaster':{'name':'Blaster','version':'test'}}
run('evidence needs context binding',evidence_missing,"missing 'checkingContextHash'")
print('All interface regressions passed.')
