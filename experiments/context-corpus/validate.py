#!/usr/bin/env python3
"""Reproduce concrete cross-interpreter checks and the separate proof calibration.

Concrete replay is deliberately not reported as a proof over all contexts.
Requires the pinned Aiken compiler, Lake/Lean, and Z3 on PATH.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess

from run import HERE, ROOT, WORK, artifacts, compile_cases
from run import sha


def command(argv, log):
    with log.open("w") as output:
        subprocess.run(argv, cwd=ROOT, stdout=output,
                       stderr=subprocess.STDOUT, check=True, timeout=120)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--compiler", default="aiken")
    parser.add_argument("--compile", action="store_true")
    parser.add_argument("--proofs", action="store_true")
    parser.add_argument("--kernel-proofs", action="store_true",
                        help="Check kernel proofs without the optional SMT calibration")
    args = parser.parse_args()
    WORK.mkdir(exist_ok=True)
    if args.compile or not (HERE / "plutus.json").exists():
        compile_cases(args.compiler)
    cases = json.loads((HERE / "cases.json").read_text())
    artifacts(cases)

    export = subprocess.run([args.compiler, "export", "--module", "context_fixture",
                             "--name", "encoded_placeholder", str(HERE)],
                            cwd=ROOT, capture_output=True, text=True, check=True, timeout=60)
    exported = json.loads(export.stdout)
    witness = WORK / "placeholder.cbor.hex"
    witness.write_text(exported["compiledCode"] + "\n")
    evaluated = subprocess.run([args.compiler, "uplc", "eval", "-c", str(witness)],
                               cwd=ROOT, capture_output=True, text=True, check=True, timeout=30)
    data_term = json.loads(evaluated.stdout)["result"]
    native = []
    for case in cases:
        output = subprocess.run([args.compiler, "uplc", "eval", "-c",
                                 str(WORK / "hex" / (case["id"] + ".hex")), data_term],
                                cwd=ROOT, capture_output=True, text=True, timeout=30)
        if output.returncode == 0:
            evaluated = json.loads(output.stdout)
            if "".join(evaluated["result"].split()) != "(conunit())":
                raise RuntimeError(f"Non-unit result for {case['id']}: {evaluated}")
            result = "accept"
        elif (output.returncode == 1 and re.search(r"Error\n-+", output.stderr)
              and re.search(r"Costs\n-+\ncpu: \d+\nmemory: \d+", output.stderr)):
            evaluated, result = {}, "reject"
        else:
            raise RuntimeError(f"Unexpected Aiken failure for {case['id']}: {output.stderr}")
        native.append(dict(case=case["id"], interpreter="aiken",
                           fixture="typed_stdlib_placeholder", result=result,
                           cpu=evaluated.get("cpu"), mem=evaluated.get("mem")))

    lean_output = WORK / "native-lean.jsonl"
    lean_output.write_text("")
    relative_output = lean_output.relative_to(ROOT).as_posix()
    source = ["import ContextCorpus.Native", "import PlutusCore.UPLC.ScriptEncoding",
              "open Lean ContextCorpus", "set_option maxHeartbeats 0",
              "set_option maxRecDepth 20000"]
    for index, case in enumerate(cases):
        path = (WORK / "hex" / (case["id"] + ".hex")).relative_to(ROOT).as_posix()
        source += [f'#import_uplc p{index} PlutusV3 single_cbor_hex "{path}"',
                   f'#eval IO.FS.withFile "{relative_output}" .append (fun f => '
                   f'f.putStrLn (Json.mkObj [("case", toJson "{case["id"]}"), '
                   f'("replay", replay p{index} (encode empty))]).compress)']
    replay = WORK / "NativeReplays.lean"
    replay.write_text("\n".join(source) + "\n")
    command(["lake", "build", "ContextCorpus.Native"], WORK / "build-native.log")
    command(["lake", "lean", str(replay)], WORK / "native-lean.log")
    lean = [json.loads(line) for line in lean_output.read_text().splitlines()]
    assert len(lean) == len(native) == len(cases)
    for aiken, cek in zip(native, lean):
        assert aiken["case"] == cek["case"]
        assert aiken["result"] == cek["replay"]["result"], (aiken, cek)
    (HERE / "native-aiken.jsonl").write_text("\n".join(json.dumps(r, separators=(",", ":")) for r in native) + "\n")
    shutil.copyfile(lean_output, HERE / "native-lean.jsonl")
    print(f"Concrete fixture: {len(cases)}/{len(cases)} interpreter results agree.", flush=True)

    checked = []
    if args.proofs or args.kernel_proofs:
        targets = ["ContextCorpus.Probe", "ContextCorpus.WireWitness",
                   "ContextCorpus.FeeKernel", "ContextCorpus.CountTheorems"]
        if args.proofs:
            targets.append("ContextCorpus.FeeProof")
        for target in targets:
            log = WORK / (target.rsplit(".", 1)[1] + ".log")
            command(["lake", "build", target], log)
            if target == "ContextCorpus.FeeProof" and "✅ Valid" not in log.read_text():
                raise RuntimeError("Missing positive solver result in fee calibration log")
            checked.append(target)
            print(f"Checked {target}; see its documented proof scope.", flush=True)

    checks = dict(compiled_manifest_sha256=sha((HERE / "compiled.jsonl").read_bytes()),
                  validation_harness_sha256=sha(Path(__file__).read_bytes()),
                  concrete_fixture="typed stdlib placeholder, not asserted ledger-valid",
                  concrete_agreements=len(cases), universal_validity_goals_proved=0,
                  checked_modules=checked,
                  formal_scope={
                      "Probe": "kernel-checked representation laws and assumption-plumbing assertions",
                      "WireWitness": "kernel-checked complete wire equality on one fixture",
                      "FeeProof": "SMT criterion for all outer fields and arbitrary spending payload",
                      "FeeKernel": "same criterion on the original CEK, kernel-checked without new axioms",
                      "CountTheorems": "four compiled spending validators: exact all-fuel semantics, unbounded lists, acceptance and adequacy; raw validity theorem conditional on encoding coverage"})
    (HERE / "checks.json").write_text(json.dumps(checks, indent=2) + "\n")


if __name__ == "__main__":
    main()
