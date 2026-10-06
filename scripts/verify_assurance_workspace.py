#!/usr/bin/env python3
"""Build and verify the coordinated local assurance workspace without global configuration changes."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--plutus',type=Path,required=True)
p.add_argument('--cips',type=Path,required=True)
p.add_argument('--z3',type=Path,required=True)
p.add_argument('--ghc',default='ghc')
p.add_argument('--output',type=Path,required=True)
p.add_argument('--ual',type=Path,help='Optional UAL specification checkout to include in provenance')
p.add_argument('--skip-build',action='store_true')
p.add_argument('--preflight-only',action='store_true')
a=p.parse_args()
core=Path(__file__).resolve().parents[1]
lock=json.loads(Path(__file__).with_name('assurance-workspace.json').read_text())
blaster=(core/lock['layout']['blaster']).resolve();ledger=(core/lock['layout']['ledger']).resolve()
a.plutus=a.plutus.resolve();a.cips=a.cips.resolve();a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=True)
(a.output/'workspace-report.json').unlink(missing_ok=True)
env=os.environ.copy();env['PATH']=str(a.z3.resolve().parent)+os.pathsep+env['PATH'];env['PYTHONDONTWRITEBYTECODE']='1'
def capture(cmd,cwd=core):return subprocess.check_output(cmd,cwd=cwd,env=env,text=True).strip()
def require(ok,message):
    if not ok:raise SystemExit(message)
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
require(capture(['git','rev-parse','HEAD'],blaster)==lock['blasterCommit'],'Blaster revision differs from assurance-workspace.json')
for repo in [core,ledger,blaster]:
    require(capture(['lake','env','lean','--version'],repo).startswith('Lean (version '+lock['lean']+',') or
            ('version '+lock['lean']+' ') in capture(['lake','env','lean','--version'],repo),'Lean version mismatch: '+str(repo))
require(capture([a.ghc,'--numeric-version'],a.plutus)==lock['ghc'],'GHC version mismatch')
require(lock['z3Version'] in capture([str(a.z3.resolve()),'--version']),'Z3 version mismatch')
probe=subprocess.run([str(a.z3.resolve()),'-in'],input='(set-simplifier recfun-finder)\n(check-sat)\n',text=True,capture_output=True,timeout=15)
require(probe.returncode==0 and probe.stdout.strip()=='sat','Z3 lacks the required recfun-finder simplifier: '+probe.stdout+probe.stderr)
for repo in [core,ledger]:
    manifest=json.loads((repo/'lake-manifest.json').read_text())
    dep=next(x for x in manifest['packages'] if x['name']=='Blaster')
    require(dep['type']=='path' and (repo/dep['dir']).resolve()==blaster,'Consumers do not resolve the same Blaster checkout')
import jsonschema  # fail early with the pinned CIP test dependency missing
print('PASS workspace revisions, toolchains, shared dependency and solver capability',flush=True)
if a.preflight_only:sys.exit(0)
results=[]
def run(name,cmd,cwd=core,timeout=1800):
    print('Running',name,flush=True)
    with (a.output/(name+'.log')).open('w') as log:
        r=subprocess.run([str(x) for x in cmd],cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
    if r.returncode:raise RuntimeError(name+' failed; see '+str(a.output/(name+'.log')))
    results.append(name);print('PASS',name,flush=True)
project='--project-file=cabal.assurance.project'
compiler='--with-compiler='+a.ghc
names=['game','parameters','auction','recursive']
if not a.skip_build:
    run('build-core',['lake','build','Blaster:shared','PlutusCore.UPLC.BlueprintEncoding.Assurance'])
    run('build-ledger',['lake','build','CardanoLedgerApi.Examples.Auction','PlutusCore.UPLC.BlueprintEncoding.Assurance'],ledger)
    run('build-plutus',['cabal','build',project,compiler,*[f'docusaurus-examples:exe:example-ual-{n}' for n in names],'plutus-tx:test:plutus-tx-test'],a.plutus,timeout=7200)
generators={n:capture(['cabal','list-bin',project,compiler,f'docusaurus-examples:exe:example-ual-{n}'],a.plutus) for n in names}
base=core/'Tests/BlueprintVerify'
# Every child captures a fresh matching environment; no historical evidence is reused.
def example(n):
    if n=='auction':return run(n,['lake','env',sys.executable,ledger/'Tests/BlueprintVerify/run_auction.py',generators[n],a.output/n],ledger)
    if n=='game':return run(n,['lake','env',sys.executable,base/'run_generated.py','--generator',generators[n],'--plutus',a.plutus,'--output',a.output/n])
    return run(n,['lake','env',sys.executable,base/f'run_{n}.py',generators[n],a.output/n])
with ThreadPoolExecutor(max_workers=2) as pool:list(pool.map(example,names))
run('generated-artifacts',[sys.executable,base/'validate_outputs.py','--cips',a.cips,*[a.output/n for n in names]])
run('cip-schemas',[sys.executable,'-m','unittest','discover','-s','CIP-XXXX/tests','-v'],a.cips)
run('legacy-regressions',['lake','env',sys.executable,base/'regression.py'])
run('interface-regressions',['lake','env',sys.executable,base/'interface_regression.py',a.output/'game'])
for name in ['RecursiveSchema','NativeEncoding','BooleanCase']:
    run(name,['lake','env','lean',base/(name+'.lean')])
testbin=capture(['cabal','list-bin',project,compiler,'plutus-tx:test:plutus-tx-test'],a.plutus)
run('ual-tests',[testbin,'-p','UAL'],a.plutus/'plutus-tx')
run('field-tests',[testbin,'-p','field names'],a.plutus/'plutus-tx')
run('tuple-tests',[testbin,'-p','List product schemas'],a.plutus/'plutus-tx')
run('definition-tests',[testbin,'-p','PlutusTx.Blueprint.Definition'],a.plutus/'plutus-tx')
source_inputs = {}
for label, root, patterns in [
    ('core', core, ['PlutusCore/UPLC/BlueprintEncoding/*.lean','PlutusCore/UPLC/BlueprintEncoding/*.schema.json','PlutusCore/UPLC/CekMachine.lean','PlutusCore/UPLC/FlatEncoding/*.lean','PlutusCore/UPLC/ScriptEncoding/*.lean','Tests/BlueprintVerify/*.py','Tests/BlueprintVerify/*.lean','scripts/*assurance*']),
    ('ledger', ledger, ['CardanoLedgerApi/Examples/*.lean','Tests/BlueprintVerify/*.py','Tests/BlueprintVerify/*.lean']),
    ('plutus', a.plutus, ['plutus-tx/src/PlutusTx/Assurance/*.hs','plutus-tx/src/PlutusTx/Ual/*.hs','plutus-tx/src/PlutusTx/Blueprint/Definition/*.hs','doc/docusaurus/static/code/Example/Ual/**/*.hs','cabal.assurance.project*','doc/docusaurus/docusaurus-examples.cabal']),
    ('cips', a.cips, ['CIP-XXXX/**/*.json','CIP-XXXX/**/*.md','CIP-XXXX/tests/*.py','CIP-0057/extensions/compiled-interface/**/*.json','CIP-0057/extensions/compiled-interface/**/*.md'])]:
    for pattern in patterns:
        for path in root.glob(pattern):
            if path.is_file(): source_inputs[label+'/'+str(path.relative_to(root))] = digest(path)
if a.ual:
    source_inputs['ual/README.md'] = digest(a.ual/'README.md')
report={'status':'passed','sourceInputs':source_inputs,'checks':results,'lock':lock,'z3Sha256':digest(a.z3.resolve()),'generatorSha256':{n:digest(g) for n,g in generators.items()},
        'repositories':{name:{'head':capture(['git','rev-parse','HEAD'],repo),'trackedDiffSha256':hashlib.sha256(subprocess.check_output(['git','-c','core.fsmonitor=false','diff','HEAD','--binary'],cwd=repo)).hexdigest()} for name,repo in [('plutus',a.plutus),('core',core),('ledger',ledger),('blaster',blaster),('cips',a.cips)]}}
(a.output/'workspace-report.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS complete workspace verification',flush=True)
