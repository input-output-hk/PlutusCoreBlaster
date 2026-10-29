#!/usr/bin/env python3
"""Profile Flat files or directories; keep raw JSON and print the main wall-time costs.

python3 scripts/profile_bench_cek.py /path/to/plutus_use_cases --runs 10
This diagnostic is separate from the benchmark's check/time CSV contract.
"""

import argparse
import json
from pathlib import Path
import platform
import subprocess


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/bench_cek"


def positive(value):
    n = int(value)
    if n <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return n


def summarize(report):
    runs = report["runs"]
    dec, ev, base = report["decode"], report["eval"], report["baseline"]
    ms = lambda ns: ns / runs / 1_000_000
    pct = lambda ns, total: 100 * ns / total if total else 0
    ratio = lambda ns, ref: f"{ns / ref:.2f}x" if ref else "n/a"
    lines = [f"### {report['script']}", "",
             f"Reference: decode **{ms(base['decode_ns']):.3f} ms**, "
             f"eval **{ms(base['eval_ns']):.3f} ms** per run. "
             f"Instrumented/reference ratio: decode {ratio(dec['total_ns'], base['decode_ns'])}, "
             f"eval {ratio(ev['total_ns'], base['eval_ns'])}.", "",
             "| Phase | ms/run | % of instrumented decode + eval |",
             "|---|---:|---:|"]
    phases = [("Bytes → string", dec["bytes_to_string_ns"]),
              ("String → bits", dec["string_to_bits_ns"]),
              ("Flat parsing", dec["flat_parse_ns"]),
              ("CEK transitions + step costing", ev["machine_ns"]),
              ("Builtin execution", ev["builtin_eval_ns"]),
              ("Builtin cost pass (inclusive)", ev["cost_pass_ns"])]
    total = dec["total_ns"] + ev["total_ns"]
    phases.append(("Other instrumentation / bookkeeping", total - sum(ns for _, ns in phases)))
    for label, ns in phases:
        lines.append(f"| {label} | {ms(ns):.3f} | {pct(ns, total):.1f}% |")
    lines += ["", f"{ev['machine_steps'] // runs:,} ordinary CEK transitions and "
              f"{ev['builtin_calls'] // runs:,} builtin calls per run. "
              f"Clock-pair median/p95: {report['clock_pair_median_ns']}/"
              f"{report['clock_pair_p95_ns']} ns.", "",
              "| Top builtin | calls/run | execution ms/run | costing ms/run |",
              "|---|---:|---:|---:|"]
    for builtin in report["builtins"][:10]:
        lines.append(f"| {builtin['builtin'].split('.')[-1]} | {builtin['calls'] // runs} | "
                     f"{ms(builtin['eval_ns']):.3f} | {ms(builtin['cost_ns']):.3f} |")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", type=Path, nargs="+")
    parser.add_argument("--runs", type=positive, default=10)
    parser.add_argument("--max-steps", type=positive, default=100_000_000)
    parser.add_argument("--timeout", type=positive, default=120, help="seconds per script")
    parser.add_argument("--output", type=Path, default=ROOT / "Benchmark/results/profile")
    args = parser.parse_args()
    paths = sorted({file.resolve() for path in args.paths for file in
                    (path.glob("*.flat") if path.is_dir() else [path])})
    if not paths or any(not path.is_file() for path in paths):
        parser.error("provide existing Flat files or directories containing *.flat")
    if len({path.stem for path in paths}) != len(paths):
        parser.error("script filenames must have unique stems")
    if not BINARY.is_file():
        parser.error("build first: lake build bench_cek")
    args.output.mkdir(parents=True, exist_ok=True)
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True))
    sections = ["# CEK diagnostic profile", "",
                f"Source: `{revision}`{' (dirty working tree)' if dirty else ''}. "
                f"Host: {platform.platform()}, {platform.machine()}. Runs: {args.runs}.", "",
                "Times are diagnostic and include instrumentation overhead. Percentages describe "
                "the instrumented run; tiny builtins near the clock floor cannot be ranked reliably. "
                "Cost pass time includes its per-call timers and statistics. CPU/mem in JSON are "
                "ledger ExUnits, distinct from nanoseconds."]
    for path in paths:
        result = subprocess.run([str(BINARY), "profile", str(path), str(args.runs), str(args.max_steps)],
                                capture_output=True, text=True, timeout=args.timeout, check=True)
        report = json.loads(result.stdout)
        (args.output / (path.stem + ".json")).write_text(result.stdout)
        summary = summarize(report)
        sections += ["", summary]
        print(summary, flush=True)
    (args.output / "summary.md").write_text("\n".join(sections) + "\n")
    print(f"\nRaw JSON and summary: {args.output.resolve()}")


if __name__ == "__main__":
    main()
