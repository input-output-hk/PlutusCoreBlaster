#!/usr/bin/env python3
"""Full-program #prep_uplc comparisons; timeout/error never counts as success.

Build imports first. Each warm child includes Lake startup and elaboration,
uses one Lean worker and a 3 GiB address-space limit. Timings are diagnostic.
"""
import argparse
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CASES = {
    "integer": ("GenericOptimizationFixture", "integerMember"),
    "bytes": ("GenericOptimizationFixture", "bytesMember"),
    "threshold": ("GenericOptimizationFixture", "integerThreshold"),
    "eager": ("AikenValidationFixture", "sample"),
}
METRICS = """
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
  let used := ci.value!.getUsedConstants
  let evaluator := used.contains `PlutusCore.UPLC.CekMachine.runSteps ||
    used.contains `PlutusCore.UPLC.CekMachine.runStepsPreservingState ||
    used.contains `PlutusCore.UPLC.CekMachine.step
  let has := used.any (fun n =>
    n.toString.startsWith "PlutusCore.UPLC.Optimize.searchPlan" ||
    n.toString.startsWith "PlutusCore.UPLC.Optimize.traversalPlan")
  Lean.logInfo m!"MEASURE nodes={nodes ci.value!} summary={has} evaluator={evaluator}"
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--budgets", nargs="+", type=int, default=[1000, 10000, 100000])
    parser.add_argument("--cases", nargs="+", choices=CASES, default=list(CASES))
    parser.add_argument("--modes", nargs="+", choices=["baseline", "generic", "combined"],
                        default=["baseline", "generic", "combined"])
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()
    work = HERE / ".work"
    work.mkdir(exist_ok=True)
    results = []
    for case in args.cases:
        namespace, script = CASES[case]
        for fuel in args.budgets:
            for mode in args.modes:
                source = "import PlutusCore.UPLC.PreProcess\n"
                source += "import Tests.UPLC.Optimize.GenericFixture\n"
                source += "import Tests.UPLC.Optimize.AikenFixture\n"
                if mode in ("generic", "combined"):
                    source += "import PlutusCore.UPLC.Optimize.Extension\n"
                if mode == "combined":
                    source += "import PlutusCore.UPLC.Optimize.Aiken.Extension\n"
                source += "open PlutusCore.UPLC.PlutusScript\n"
                source += f"open Tests.{namespace}\n"
                source += "set_option maxHeartbeats 0\nset_option maxRecDepth 20000\n"
                if case == "eager":
                    source += "def sample : PlutusScript := ⟨.PlutusV3, script⟩\n"
                source += f"#prep_uplc prepared {script} params {fuel}\n" + METRICS
                path = work / f"{case}-{mode}-{fuel}.lean"
                path.write_text(source)
                start = time.monotonic()
                with path.with_suffix(".log").open("w") as log:
                    def limit():
                        resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))

                    proc = subprocess.Popen(
                        ["lake", "lean", str(path), "--", "--threads=1"], cwd=ROOT,
                        stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
                        preexec_fn=limit)
                    try:
                        proc.wait(timeout=args.timeout)
                        status = "ok" if proc.returncode == 0 else "error"
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
                        status = "timeout"
                text = path.with_suffix(".log").read_text()
                match = re.search(r"MEASURE nodes=(\d+) summary=(true|false) evaluator=(true|false)", text)
                result = dict(case=case, mode=mode, fuel=fuel, status=status,
                              wall_seconds=round(time.monotonic() - start, 3))
                if match:
                    result.update(nodes=int(match[1]), summary=match[2] == "true", evaluator=match[3] == "true")
                    if mode != "baseline" and result["evaluator"]:
                        result["status"] = "residual_evaluator"
                results.append(result)
                (HERE / "results.json").write_text(json.dumps(results, indent=2) + "\n")
                print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
