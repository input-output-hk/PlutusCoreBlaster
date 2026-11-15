#!/usr/bin/env python3
"""Compare ordinary #prep_uplc with/without the optional PR472 rules.
Counts residual expressions and summary calls; timings include module loading.
"""
import argparse,json,os,re,signal,subprocess,time,resource
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
METRICS="""
partial def nodes (root : Lean.Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    unless seen.contains e do
      seen := seen.insert e
      match e with
      | .app f a => todo := f :: a :: todo
      | .lam _ t b _ | .forallE _ t b _ => todo := t :: b :: todo
      | .letE _ t v b _ => todo := t :: v :: b :: todo
      | .mdata _ b | .proj _ _ b => todo := b :: todo
      | _ => pure ()
  return seen.size
run_cmd do
  let ci ← Lean.getConstInfo `prepared.prop
  let e := ci.value!
  let has := e.getUsedConstants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.Aiken.ValidationPlan" || n == `PlutusCore.UPLC.Optimize.Aiken.validationSummary || n == `PlutusCore.UPLC.Optimize.Aiken.validationPlan)
  Lean.logInfo m!"MEASURE nodes={nodes e} summary={has}"
"""
def main():
 p=argparse.ArgumentParser();p.add_argument('--budgets',nargs='+',type=int,default=[1000,10000,100000]);p.add_argument('--timeout',type=int,default=60);a=p.parse_args()
 work=HERE/'.work';work.mkdir(exist_ok=True)
 results=[]
 for n in a.budgets:
  for mode in ['baseline','optimized']:
   src='import Tests.UPLC.Optimize.AikenFixture\nimport PlutusCore.UPLC.PreProcess\n'
   if mode=='optimized':src+='import PlutusCore.UPLC.Optimize.Aiken.Extension\n'
   src+='open PlutusCore.UPLC.PlutusScript\nopen Tests.AikenValidationFixture\nset_option maxRecDepth 20000\nset_option maxHeartbeats 0\n'
   src+='def sample : PlutusScript := ⟨.PlutusV3, script⟩\n'
   src+=f'#prep_uplc prepared sample params {n}\n'+METRICS
   path=work/f'{mode}-{n}.lean';path.write_text(src)
   start=time.monotonic()
   with (work/f'{mode}-{n}.log').open('w') as log:
    def limit(): resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
    proc=subprocess.Popen(['lake','env','lean','--threads=1',str(path)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limit)
    try:proc.wait(timeout=a.timeout);status='ok' if proc.returncode==0 else 'error'
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();status='timeout'
   text=(work/f'{mode}-{n}.log').read_text();m=re.search(r'MEASURE nodes=(\d+) summary=(true|false)',text)
   r=dict(mode=mode,fuel=n,status=status,wall_seconds=round(time.monotonic()-start,3))
   if m:r.update(nodes=int(m[1]),summary=m[2]=='true')
   results.append(r);print(json.dumps(r),flush=True)
 (HERE/'results.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
