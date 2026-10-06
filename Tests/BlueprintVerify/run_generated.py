#!/usr/bin/env python3
"""Run a built UAL game generator and fresh Blaster checks, recording provenance.
Usage: lake env python3 Tests/BlueprintVerify/run_generated.py --generator EXE --plutus REPO --output DIR
Run from the PlutusCoreBlaster repository after `lake build PlutusCore.UPLC.BlueprintEncoding.Assurance`.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import zipfile
import shutil
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--generator', required=True, type=Path)
p.add_argument('--plutus', required=True, type=Path)
p.add_argument('--output', required=True, type=Path)
a = p.parse_args()
from runtime import lean_command
lean_args = lean_command()

repo = Path(__file__).resolve().parents[2]
out = a.output.resolve()
out.mkdir(parents=True, exist_ok=True)
generator = a.generator.resolve()
lean = os.environ.get('LEAN', 'lean')

def capture(command, cwd=repo):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def revision(path):
    path = path.resolve()
    patch = subprocess.check_output(['git', '-c', 'core.fsmonitor=false', 'diff', 'HEAD', '--binary'], cwd=path)
    return {'commit':capture(['git','rev-parse','HEAD'], path),
            'trackedDiffSha256':hashlib.sha256(patch).hexdigest(),
            'status':capture(['git','-c','core.fsmonitor=false','status','--porcelain','--untracked-files=no'], path)}

# Clear the old report before any step can fail; stale success must not survive.
report_path = out/'run-report.json'
report_path.unlink(missing_ok=True)
(out/'verified-assurance.json').unlink(missing_ok=True)
(out/'verification-artifact.zip').unlink(missing_ok=True)
for name in ['plutus.json', 'assurance.json']:
    (out/name).unlink(missing_ok=True)
env_driver = out/'Environment.lean'
env_driver.write_text('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'
                      f'#write_checking_environment {json.dumps(str(out/"environment.json"))}\n')
subprocess.run(lean_args + [str(env_driver)], cwd=repo, check=True, timeout=300)
subprocess.run([str(generator), 'environment.json'], cwd=out, check=True, timeout=120)
assurance = json.loads((out/'assurance.json').read_text())
blueprint = json.loads((out/'plutus.json').read_text())
assert assurance['blueprint']['hash'] == {'alg':'sha256','digest':digest(out/'plutus.json')}
assert {x['id'] for x in assurance['properties']} == {'correct_guess','wrong_guess','malformed_datum'}
assert all(not x.get('evidence') for x in assurance['properties'])
check = out/'Check.lean'
check.write_text('import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'
                 f'#verify_blueprint Game {json.dumps(str(out/"assurance.json"))}\n')
result = subprocess.run(lean_args + [str(check)], cwd=repo, text=True, capture_output=True, timeout=300)
log = result.stdout + result.stderr
(out/'verification.log').write_text(log)
print(log, end='')
verified = re.findall(r"Property '([^']+)': verified \(Blaster SMT", log)
expected = {x['id'] for x in assurance['properties']}
if result.returncode != 0 or set(verified) != expected or len(verified) != len(expected):
    raise SystemExit('Fresh verification failed or skipped a property; see verification.log')

# Keep evaluation of the concrete SHA-256 vector separate from the SMT model.
eval_source = (repo/'Tests/BlueprintVerify/Game/EvaluateInterface.lean').read_text()
eval_source = eval_source.replace('"Tests/BlueprintVerify/Game/plutus.json"', json.dumps(str(out/'plutus.json')))
eval_path = out/'Evaluate.lean'; eval_path.write_text(eval_source)
evaluated = subprocess.run(lean_args + [str(eval_path)], cwd=repo, text=True, capture_output=True, timeout=120)
(out/'evaluation.log').write_text(evaluated.stdout+evaluated.stderr)
if evaluated.returncode:
    raise SystemExit('Concrete hash-vector evaluation failed; see evaluation.log')
blaster = repo.parent/'Lean-blaster'
tracked_inputs = ['PlutusCore/UPLC/BlueprintEncoding/Assurance.lean',
                  'PlutusCore/UPLC/BlueprintEncoding/Basic.lean',
                  'PlutusCore/UPLC/BlueprintEncoding/Schema.lean',
                  'PlutusCore/UPLC/BlueprintEncoding/assurance.schema.json',
                  'PlutusCore/UPLC/BlueprintEncoding/assurance-v2.schema.json',
                  'PlutusCore/UPLC/BlueprintEncoding/checking-context.schema.json',
                  'PlutusCore/UPLC/BlueprintEncoding/interface.schema.json',
                  'PlutusCore/UPLC/BlueprintEncoding/value.schema.json',
                  'PlutusCore/UPLC/BlueprintEncoding/blueprint.schema.json',
                  'PlutusCore/UPLC/CekMachine.lean', 'PlutusCore/UPLC/Utils.lean',
                  'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'Tests/BlueprintVerify/runtime.py']
report = {'format':'ual-blaster-run-2', 'created':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'method':'Blaster SMT; no reconstructed Lean proof',
          'verifiedProperties':verified, 'concreteHashVector':'passed',
          'inputs':{f.name:digest(f) for f in out.glob('*.json') if f.name not in ['run-report.json', 'verified-assurance.json']},
          'generatorSha256':digest(generator),
          'generatorSourceSha256':digest(a.plutus/'doc/docusaurus/static/code/Example/Ual/Game/Main.hs'),
          'environment':{'lean':capture([lean,'--version']), 'z3':capture(['z3','-version']),
                         'plutus':revision(a.plutus), 'PlutusCoreBlaster':revision(repo),
                         'Blaster':revision(blaster), 'CardanoLedgerApiBlaster':None,
                         'sha256Utility':shutil.which('sha256sum') or shutil.which('shasum') or 'pure Lean fallback',
                         'solverOptions':{'timeoutSeconds':60},
                         'checkerInputs':{f:digest(repo/f) for f in tracked_inputs}},
          'checkingContexts':{key:json.loads((out/ref['uri']).read_text()) for key,ref in assurance['checkingContexts'].items()},
          'logSha256':digest(out/'verification.log')}
report_path.write_text(json.dumps(report,indent=2)+'\n')
# Package the exact check inputs, logs, modified sources, and reproduction recipe.
artifact = out/'verification-artifact.zip'
with zipfile.ZipFile(artifact,'w',compression=zipfile.ZIP_DEFLATED) as archive:
    for name in ['plutus.json','assurance.json','Check.lean','Evaluate.lean','verification.log','evaluation.log','run-report.json']:
        archive.write(out/name,name)
    for path in [out/'environment.json', out/'Environment.lean', *out.glob('checking-*.json')]:
        archive.write(path, path.name)
    for name in tracked_inputs:
        archive.write(repo/name,'checker/'+name)
    archive.write(Path(__file__), 'checker/Tests/BlueprintVerify/run_generated.py')
    archive.write(repo/'Tests/BlueprintVerify/Game/EvaluateInterface.lean','checker/Tests/BlueprintVerify/Game/EvaluateInterface.lean')
    archive.write(a.plutus/'doc/docusaurus/static/code/Example/Ual/Game/Main.hs','generator/Main.hs')
    archive.write(a.plutus/'plutus-tx/src/PlutusTx/Assurance/Interface.hs',
                  'generator/plutus-tx/src/PlutusTx/Assurance/Interface.hs')
    for name,path in [('plutus',a.plutus),('PlutusCoreBlaster',repo),('Blaster',blaster)]:
        patch=subprocess.check_output(['git','-c','core.fsmonitor=false','diff','HEAD','--binary'],cwd=path)
        archive.writestr(f'reproduction/{name}.patch',patch)
    archive.writestr('REPRODUCE.txt',
        'Use the commits, versions, execution settings, and source hashes in run-report.json.\n'
        'Apply reproduction/*.patch to their respective repositories; overlay checker/ sources.\n'
        'Overlay generator/plutus-tx/ onto the Plutus plutus-tx/ directory.\n'
        'Copy generator/Main.hs to doc/docusaurus/static/code/Example/Ual/Game/Main.hs in Plutus.\n'
        'Build docusaurus-examples:exe:example-ual-game in the pinned Plutus build environment.\n'
        'In PlutusCoreBlaster: lake build PlutusCore.UPLC.BlueprintEncoding.Assurance\n'
        'Then lake env python3 Tests/BlueprintVerify/run_generated.py --generator EXE --plutus REPO --output DIR\n'
        'Check the blueprint hash against run-report.json. The artifact is a local SMT run record, not a kernel proof.\n'
        'The generator binary is identified by hash, not bundled. Platform-specific builds may have different binary hashes.\n')
assurance['tools'] = {'blaster':{'name':'Blaster', 'version':report['environment']['Blaster']['commit'],
                                'uri':'https://github.com/input-output-hk/Lean-blaster'}}
script_hash = blueprint['validators'][0]['hash']
for prop in assurance['properties']:
    prop['evidence'] = [{'method':'smt-check', 'verifier':'Local Blaster runner', 'tool':'blaster',
                         'outcome':'verified', 'date':report['created'][:10], 'scriptHash':script_hash,
                         'checkingContextHash':assurance['checkingContexts'][prop['checkingContext']]['hash'],
                         'artifact':{'uri':artifact.name,'hash':{'alg':'sha256','digest':digest(artifact)},
                                     'mediaType':'application/zip'},
                         'notes':'Fresh SMT verification; trusts the translation and solver. No reconstructed Lean proof. The hash vector is a separate execution check.'}]
(out/'verified-assurance.json').write_text(json.dumps(assurance,indent=2,ensure_ascii=False)+'\n')
print(f'Recorded fresh verification: {report_path}')
print(f'Wrote evidence-bearing assurance: {out/"verified-assurance.json"}')
