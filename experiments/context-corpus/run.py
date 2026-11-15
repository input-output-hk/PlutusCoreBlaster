#!/usr/bin/env python3
"""Compile independent Aiken programs and probe unchanged PR93 optimizations.

raw: all Data contexts; view: all 18 outer-shape fields; assumed: raw Data
with an explicit outer-shape hypothesis seeded before optimization. None of
these modes claims to implement or prove the missing isValidContext contract.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import runpy
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORK = HERE / ".work"
NODE_COUNTER = runpy.run_path(str(HERE.parent / "generic-optimizations/bench.py"))["METRICS"].split("run_cmd do")[0]


def sha(content):
    return hashlib.sha256(content).hexdigest()


def compile_cases(compiler):
    with (WORK / "compile.log").open("w") as log:
        subprocess.run([compiler, "build", "--uplc", str(HERE)], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True)


def artifacts(cases):
    bp = json.loads((HERE / "plutus.json").read_text())
    (WORK / "hex").mkdir(exist_ok=True)
    records = []
    for case in cases:
        title = f"{case['id']}.{case['id']}." + ("else" if case["purpose"] == "any" else "spend")
        v = next(v for v in bp["validators"] if v["title"] == title)
        (WORK / "hex" / (case["id"] + ".hex")).write_text(v["compiledCode"] + "\n")
        uplc = (HERE / "artifacts" / (title + ".uplc")).read_text()
        records.append(dict(id=case["id"], title=title, script_hash=v["hash"],
                            source_sha256=sha((HERE / case["source"]).read_bytes()),
                            compiled_sha256=sha(bytes.fromhex(v["compiledCode"])),
                            bytes=len(v["compiledCode"]) // 2,
                            lambdas=len(re.findall(r"\(lam\s", uplc)),
                            builtins=dict(sorted(Counter(re.findall(r"\(\s*builtin\s+(\w+)", uplc)).items()))))
    (HERE / "compiled.jsonl").write_text("\n".join(json.dumps(r, separators=(",", ":")) for r in records) + "\n")
    return {r["id"]: r for r in records}


def source(case, mode, engine, fuel):
    imports = ["import PlutusCore.UPLC.CekMachine", "import ContextCorpus.Boundary", "import ContextCorpus.UnderAssumptions",
               "import PlutusCore.UPLC.ScriptEncoding"]
    if mode == "assumed":
        imports.append("import ContextCorpus.BoundaryRules")
    if engine == "generic":
        imports.append("import PlutusCore.UPLC.Optimize.Extension")
    script_path = (WORK / "hex" / (case["id"] + ".hex")).relative_to(ROOT)
    src = "\n".join(imports) + "\nopen Lean Elab Command Term Meta ContextCorpus\n"
    src += "set_option maxHeartbeats 0\nset_option maxRecDepth 20000\n"
    src += f'#import_uplc script PlutusV3 single_cbor_hex "{script_path}"\n' + NODE_COUNTER
    if mode == "view":
        term = f"fun (v : View) => PlutusCore.UPLC.CekMachine.cekExecuteProgram script.script (viewArgs v) {fuel}"
    elif mode == "assumed":
        term = f"fun (d : PlutusCore.Data.Data) (_h : WellShaped d) => PlutusCore.UPLC.CekMachine.cekExecuteProgram script.script (rawArgs d) {fuel}"
    else:
        term = f"fun (d : PlutusCore.Data.Data) => PlutusCore.UPLC.CekMachine.cekExecuteProgram script.script (rawArgs d) {fuel}"
    optimization = "optimizeUnderAssumptions e" if mode == "assumed" else "(Blaster.Optimize.Optimize.main e).run' default"
    src += f"""
run_cmd do
  runTermElabM fun _ => do
    let e ← elabTermAndSynthesize (← `({term})) none
    let start ← IO.monoMsNow
    let out ← {optimization}
    let elapsed := (← IO.monoMsNow) - start
    let constants := out.getUsedConstants
    let evaluator := constants.contains `PlutusCore.UPLC.CekMachine.runSteps ||
      constants.contains `PlutusCore.UPLC.CekMachine.step
    let traversal := constants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.traversalPlan")
    let search := constants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.searchPlan")
    let mut body := out.consumeMData
    while body.isLambda do body := body.bindingBody!.consumeMData
    let exhausted := body.isConstOf `PlutusCore.UPLC.CekMachine.State.BudgetExhausted
    let result := Json.mkObj [("nodes", toJson (nodes out)), ("optimization_ms", toJson elapsed),
      ("evaluator", toJson evaluator), ("traversal", toJson traversal),
      ("search", toJson search), ("always_budget_exhausted", toJson exhausted)]
    logInfo m!"CORPUS_RESULT {{result.compress}}"
"""
    return src


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--compiler", default="aiken")
    parser.add_argument("--compile", action="store_true")
    parser.add_argument("--cases", nargs="*")
    parser.add_argument("--modes", nargs="+", choices=["raw", "view", "assumed"], default=["raw", "view"])
    parser.add_argument("--engines", nargs="+", choices=["baseline", "generic"], default=["baseline", "generic"])
    parser.add_argument("--fuel", nargs="+", type=int, default=[1000])
    parser.add_argument("--timeout", type=int, default=8)
    parser.add_argument("--output", default="results.jsonl")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    WORK.mkdir(exist_ok=True)
    if args.compile or not (HERE / "plutus.json").exists():
        compile_cases(args.compiler)
    cases = json.loads((HERE / "cases.json").read_text())
    metadata = artifacts(cases)
    if args.cases:
        unknown = set(args.cases) - {c["id"] for c in cases}
        if unknown:
            parser.error(f"Unknown cases: {sorted(unknown)}")
        cases = [c for c in cases if c["id"] in args.cases]
    output = HERE / args.output
    prior = [json.loads(line) for line in output.read_text().splitlines()] if args.resume and output.exists() else []
    done = {(r["case"], r["mode"], r["engine"], r["fuel"]) for r in prior}
    if not args.resume:
        output.write_text("")
    for case in cases:
        for mode in args.modes:
            for engine in args.engines:
                for fuel in args.fuel:
                    key = case["id"], mode, engine, fuel
                    if key in done:
                        continue
                    path = WORK / ("-".join(map(str, key)) + ".lean")
                    path.write_text(source(case, mode, engine, fuel))
                    start = time.monotonic()
                    with path.with_suffix(".log").open("w") as log:
                        def limit():
                            resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))

                        p = subprocess.Popen(["lake", "lean", str(path), "--", "--threads=1"], cwd=ROOT,
                                             stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
                                             preexec_fn=limit)
                        try:
                            p.wait(timeout=args.timeout)
                            status = "ok" if p.returncode == 0 else "error"
                        except subprocess.TimeoutExpired:
                            os.killpg(p.pid, signal.SIGKILL)
                            p.wait()
                            status = "timeout"
                    text = path.with_suffix(".log").read_text()
                    result = dict(case=case["id"], mode=mode, engine=engine, fuel=fuel,
                                  status=status, wall_seconds=round(time.monotonic() - start, 3),
                                  proof_status="not_attempted", compiled_sha256=metadata[case["id"]]["compiled_sha256"])
                    match = re.search(r"CORPUS_RESULT (\{[^\n]+\})", text)
                    if match:
                        result.update(json.loads(match[1]))
                    if status == "error":
                        result["error"] = text[-1000:]
                    with output.open("a") as log:
                        log.write(json.dumps(result, separators=(",", ":")) + "\n")
                    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
