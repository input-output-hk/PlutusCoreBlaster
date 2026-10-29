#!/usr/bin/env python3
"""Exercise the compiled CLI, optionally compare a pinned Plutus VM Benchmark corpus.

python3 scripts/test_bench_cek.py [--benchmark-root /path/to/plutus-vm-benchmark]
The optional corpus check writes the upstream-compatible check CSV to --output.
"""

import argparse
import csv
import io
import json
import math
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/bench_cek"
VM = "plutuscore-lean"
CHECK_FIELDS = ["vm", "script", "status", "cpu", "mem"]
TIME_FIELDS = ["vm", "script", "mean_ns", "median_ns", "min_ns", "max_ns", "stddev_ns", "iterations"]


def run(*args, timeout=120):
    return subprocess.run([str(BINARY), *map(str, args)], capture_output=True, text=True, timeout=timeout)


class NativeCliTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def flat(self, name, hex_bytes):
        path = self.root / (name + ".flat")
        path.write_bytes(bytes.fromhex(hex_bytes))
        return path

    def test_binary_decode_and_startup_cost(self):
        # UPLC integer 21; its final byte 0x81 must survive raw binary loading.
        path = self.flat('constant,"21', "010000480a81")
        result = run("check", path)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(next(csv.reader(io.StringIO(result.stdout))),
                         [VM, 'constant,"21', "ok", "16100", "200"])

    def test_builtin_costing(self):
        # addInteger 16 26, from Tests/UPLC/FlatEncoding/Tests.lean.
        path = self.flat("add", "01000033700901024069")
        result = run("check", path)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), VM + ",add,ok,181308,602")

    def test_cek_error_is_a_checked_outcome(self):
        path = self.flat("error", "01000061")
        result = run("check", path)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), VM + ",error,error,100,100")
        result = run("time", path, "d3,eval", 1)
        self.assertEqual(result.returncode, 1)
        self.assertNotIn("PVB_RESULT", result.stdout)

    def test_decode_failure_and_exhaustion_are_not_cek_errors(self):
        malformed = self.flat("malformed", "ff")
        constant = self.flat("constant", "010000480a81")
        omega = self.flat("omega", "010000323001001230010011")
        for args in [("check", malformed), ("check", constant, 1), ("check", omega, 100)]:
            result = run(*args)
            self.assertEqual(result.returncode, 1, result)
            self.assertEqual(result.stdout, "")
        self.assertIn("step limit exhausted", result.stderr)

    def test_loop_selection_order_and_statistics(self):
        path = self.flat("constant", "010000480a81")
        for loops, expected in [("eval,d3", ["d3", "eval"]), ("eval", ["eval"]), ("d3", ["d3"])]:
            result = run("time", path, loops, 1)
            self.assertEqual(result.returncode, 0, result.stderr)
            rows = [line.split(" ", 2) for line in result.stdout.splitlines() if line.startswith("PVB_RESULT ")]
            self.assertEqual([row[1] for row in rows], expected)
            for _, _, raw in rows:
                row = dict(zip(TIME_FIELDS, next(csv.reader([raw]))))
                self.assertEqual((row["vm"], row["script"]), (VM, "constant"))
                # The upstream report calls int(), so decimal nanoseconds are incompatible.
                values = {key: int(row[key]) for key in TIME_FIELDS[2:]}
                self.assertTrue(all(math.isfinite(x) for x in values.values()))
                self.assertGreater(values["mean_ns"], 0)
                self.assertGreaterEqual(values["iterations"], 50)
                self.assertGreaterEqual(values["mean_ns"] * values["iterations"],
                                        1_000_000 - values["iterations"] / 2 - 1)
                self.assertLessEqual(values["min_ns"], values["median_ns"])
                self.assertLessEqual(values["median_ns"], values["max_ns"])
                self.assertGreaterEqual(values["stddev_ns"], 0)

    def test_invalid_arguments(self):
        for args in [(), ("unknown",), ("check", "x", "0"),
                     ("profile", "x", "0"), ("profile", "x", "1", "0"),
                     ("time", "x", "check", "1"), ("time", "x", "", "1"),
                     ("time", "x", "d3", "0"), ("time", "x", "d3", "x")]:
            result = run(*args)
            self.assertEqual(result.returncode, 2, result)

    def test_profile_accounting_and_reference_equivalence(self):
        for name, flat, steps, builtin_calls, cpu, mem, status in [
            ("constant", "010000480a81", 2, 0, 16100, 200, "ok"),
            ("add", "01000033700901024069", 10, 1, 181308, 602, "ok"),
            ("error", "01000061", 1, 0, 100, 100, "error"),
        ]:
            with self.subTest(name=name):
                path = self.flat(name, flat)
                result = run("profile", path, 2)
                self.assertEqual(result.returncode, 0, result.stderr)
                report = json.loads(result.stdout)
                self.assertEqual((report["schema_version"], report["runs"]), (1, 2))
                self.assertEqual((report["script"], report["status"], report["cpu"], report["mem"]),
                                 (name, status, cpu, mem))
                ev, dec = report["eval"], report["decode"]
                self.assertEqual(ev["machine_steps"] + ev["builtin_calls"], steps * 2)
                self.assertEqual(ev["builtin_calls"], builtin_calls * 2)
                self.assertEqual(ev["builtin_calls"], sum(b["calls"] for b in report["builtins"]))
                for kind in ("eval", "cost"):
                    self.assertEqual(ev[f"builtin_{kind}_ns"],
                                     sum(b[f"{kind}_ns"] for b in report["builtins"]))
                self.assertGreaterEqual(ev["cost_pass_ns"], ev["builtin_cost_ns"])
                self.assertGreaterEqual(ev["total_ns"],
                                        ev["machine_ns"] + ev["builtin_eval_ns"] + ev["cost_pass_ns"])
                self.assertGreaterEqual(dec["total_ns"], sum(dec[key] for key in
                    ("bytes_to_string_ns", "string_to_bits_ns", "flat_parse_ns")))
                self.assertTrue(all(value >= 0 for value in ev.values()))
                if builtin_calls:
                    self.assertEqual(report["builtins"][0]["builtin"].split(".")[-1], "AddInteger")

    def test_profile_rejects_malformed_and_fuel_exhaustion(self):
        for name, flat, fuel in [("malformed", "ff", 100),
                                 ("constant", "010000480a81", 1),
                                 ("omega", "010000323001001230010011", 100)]:
            result = run("profile", self.flat(name, flat), 1, fuel)
            self.assertEqual(result.returncode, 1, result)
            self.assertEqual(result.stdout, "")


def check_corpus(benchmark_root, output, profile_corpus=False):
    data = benchmark_root / "data/plutus_use_cases"
    reference = benchmark_root / "check/reference/haskell-check.csv"
    with reference.open(newline="") as handle:
        expected = {row["script"]: row for row in csv.DictReader(handle)}
    names = {path.stem for path in data.glob("*.flat")}
    if not expected or names != set(expected):
        raise SystemExit("corpus files and reference script names differ (or are empty)")
    output.parent.mkdir(parents=True, exist_ok=True)
    profile_dir = output.parent / "profiles"
    if profile_corpus:
        profile_dir.mkdir(parents=True, exist_ok=True)
    failures = []
    with output.open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(CHECK_FIELDS)
        for index, name in enumerate(sorted(expected), 1):
            try:
                result = run("check", data / (name + ".flat"))
                rows = list(csv.reader(io.StringIO(result.stdout)))
                if result.returncode or len(rows) != 1 or len(rows[0]) != 5:
                    raise ValueError(result.stderr.strip() or "missing/invalid check row")
                row = dict(zip(CHECK_FIELDS, rows[0]))
                if row["vm"] != VM or row["script"] != name:
                    raise ValueError("wrong VM or script name in check row")
                if profile_corpus:
                    result = run("profile", data / (name + ".flat"), 1)
                    if result.returncode:
                        raise ValueError("profile failed: " + result.stderr.strip())
                    profile = json.loads(result.stdout)
                    if profile["vm"] != VM or profile["script"] != name or any(
                        str(profile[field]) != row[field] for field in ("status", "cpu", "mem")
                    ):
                        raise ValueError("profile status/ExUnits differ from check")
                    (profile_dir / (name + ".json")).write_text(result.stdout)
                writer.writerow(rows[0])
                if any(row[field] != expected[name][field] for field in ("status", "cpu", "mem")):
                    failures.append(name + ": " + repr(row) + " != " + repr(expected[name]))
            except (subprocess.TimeoutExpired, ValueError, KeyError) as error:
                writer.writerow([VM, name, "error", "", ""])
                failures.append(name + ": " + str(error))
            handle.flush()
            if index % 10 == 0:
                print(f"Checked {index}/{len(expected)} scripts", flush=True)
    for failure in failures:
        print(failure)
    print(f"Haskell gate: {len(expected) - len(failures)}/{len(expected)} match; {output}")
    if profile_corpus:
        print(f"Profile equivalence checked for the same corpus; {profile_dir}")
    return not failures


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark-root", type=Path)
    parser.add_argument("--profile-corpus", action="store_true",
                        help="also check instrumented final state and ExUnits for every script")
    parser.add_argument("--output", type=Path, default=ROOT / "Benchmark/results/cek/plutuscore-lean-check.csv")
    args = parser.parse_args()
    if args.profile_corpus and not args.benchmark_root:
        parser.error("--profile-corpus requires --benchmark-root")
    if not BINARY.is_file():
        parser.error("build the native executable first: lake build bench_cek")
    tests = unittest.defaultTestLoader.loadTestsFromTestCase(NativeCliTests)
    if not unittest.TextTestRunner(verbosity=2).run(tests).wasSuccessful():
        raise SystemExit(1)
    if args.benchmark_root and not check_corpus(args.benchmark_root.resolve(), args.output.resolve(),
                                               args.profile_corpus):
        raise SystemExit(1)
