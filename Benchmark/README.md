# `#prep_uplc` benchmarks

This suite measures the time and memory of the `#prep_uplc` command
(`PlutusCore/UPLC/PreProcess.lean`) on every script of the repository, the conformance suite
included. It also times the compiled CEK machine on the same programs. It compares runs, e.g.
before and after a change to Blaster or to the CEK machine.

```sh
make bench_prep_uplc                                  # all 885 cases, one at a time: ~1.5 h
make bench_prep_uplc JOBS=8                           # ~15 min, noisier
make bench_prep_uplc BENCH_ARGS="--suite repo,symbolic"
lake exe bench_prep_uplc list --filter example/       # which cases a selection runs
lake exe bench_prep_uplc run --filter example/factorial --runs 5
make bench_prep_uplc_compare BASE=Benchmark/results/<run-a> NEW=Benchmark/results/<run-b>
```

`lake exe bench_prep_uplc help` lists every option. Those durations are from a 32-core
machine. Most of that time goes to Lean's startup (about 1.2 s per case) and to the 5 cases
that reach the 10-minute timeout: 4 `countSetBits` conformance programs and one symbolic
validator.

Requirements:

- The conformance cases need the `.plutus-conformance` symlink, as for
  `make gen_conformance_tests`. Without it, pass `--suite repo,symbolic`.
- Memory is measured through `/proc`, so memory figures need Linux. Elsewhere, the peak is the
  whole process's and the other memory columns stay empty.

## What is measured

Each case is a generated Lean file that runs one harness command,
`#bench_prep_uplc` or `#bench_prep_uplc_file` (`PrepUplc/Harness.lean`). The harness first
imports or wraps the script, then times one `#prep_uplc` command. The timed region is the whole
command:

- the Blaster optimization;
- `inferType` of the optimized term;
- the kernel checks of `….prop` and of the `PrepUPLC.…` structure instance, which embeds the
  optimized term a second time;
- the compilation of `….exec`.

It does not include Lean's startup, the imports (about 1.1 s and 1.2 GB resident), decoding the
script, or the harness's other work.

For closed programs, meaning every case except the symbolic ones, the harness also runs the
compiled `cekExecuteProgram` on the program with the same step budget. This run happens before
and apart from `#prep_uplc`. The harness times it, taking the best of repeated runs: at least
one, then more until 50 ms or 1000 runs have passed. It also records how the run ends and how many
machine steps it takes.

The measured command runs with `Elab.async` off. Otherwise `lean` runs the kernel checks and the
compilation in background tasks, outside any timer. It also runs with `maxHeartbeats 0`.
Heartbeats are not reported: the Blaster optimizer resets the counter while it runs.

| column | meaning |
| --- | --- |
| `status` | `ok`; `import_error` (the script does not decode); `prep_error` (`#prep_uplc` failed; see `error`); `timeout`, `mem_limit` (stopped by the driver); `crash` (the process died before reporting); `no_result` |
| `wall_ms`, `wall_ms_median` | wall time of `#prep_uplc`: best and median over `--runs` |
| `cpu_ms` | user + system CPU time of the process during the best run |
| `rss_before_kb`, `peak_rss_kb`, `rss_after_kb` | resident set size before, at the peak of, and after `#prep_uplc`. The peak is `VmHWM`, reset through `/proc/self/clear_refs` just before the run. |
| `peak_delta_kb` | `peak_rss_kb − rss_before_kb`, the memory `#prep_uplc` needed. It includes the pages of the memory-mapped `.olean` files it touched. |
| `native_result` | how `cekExecuteProgram` ends on a closed program: `halt`, `error`, or `exhausted` when its `Error` comes from running out of fuel (so `#prep_uplc` sees an error too) |
| `cek_steps` | the machine steps of that run, counted by iterating `step`. Empty when that count ends differently from `cekExecuteProgram`, e.g. after a change to `runSteps`. |
| `native_ms`, `native_runs` | best time of `cekExecuteProgram` on the program, and how many runs it is the best of |
| `prep_steps_per_s`, `native_steps_per_s` | `cek_steps` per second of `#prep_uplc` and of the native run. The `#prep_uplc` rate is given only for the closed programs it fully evaluates, since otherwise it did not take all these steps. It includes the fixed cost of about 0.2 s, so it means something only for programs of thousands of steps. |
| `prop_head`, `prop_objs` | head constant of the optimized term, under its binders, and its size in distinct objects (`Expr.numObjs`). A closed program is fully evaluated when this head is the state it natively ends in. `summary.md` lists the cases where it isn't. |
| `prop_hash` | `Expr.hash` of the optimized term (32 bits). It changes whenever the term does, barring collisions. |
| `process_s`, `exit_code`, `max_rss_observed_kb` | the whole `lean` process, as the driver saw it (it samples memory every 200 ms) |

## Cases

| suite | cases | what |
| --- | --- | --- |
| `conformance` | 844 | Every program the conformance tests under `Tests/Conformance/Generated` import (`#import_uplc`, not the `…_expected` one). This is 662 expected successes and 182 expected evaluation failures. Parse-error tests import nothing and are skipped, and so are the categories the suite was generated without (`--exclude-not-implemented`). Run with no inputs and `--max-steps` (default 100000). |
| `repo` | 25 | `repoScripts` in `PrepUplc/Driver/Cases.lean`, run with no inputs, plus 6 concrete calls such as `saturate(100)`. |
| `symbolic` | 16 | The 13 validators and functions among `repoScripts`, applied to free `Data` or `Integer` arguments (`PrepUplc/Inputs.lean`), once per `--symbolic-steps` budget (default 2000), and also at the step budget of the proof a function comes from. |

The `repo` scripts:

- the script files of `PlutusCore/UPLC/ScriptEncoding/Tests{Text,Flat}`. `factorial.uplc`,
  `fibonacci.uplc` and `dataMap.flat` are also conformance programs, and `dataMap.flat` is really
  single-CBOR hex;
- the `Program`s `test1` and `test3`–`test10` of `PlutusCore/UPLC/ScriptEncoding/Tests.lean`.
  test3–test9 are real validators; test7 is identical to test6; test1, test10 and
  `testUplc.flat` are the same toy program;
- three validators copied into `PrepUplc/Scripts/` from the unnamed `example`s of
  `PlutusCore/UPLC/ScriptEncoding/Tests.lean`, which a benchmark cannot refer to:

  | file | origin | UPLC | size |
  | --- | --- | --- | --- |
  | `aiken-validator-v1.cbor.hex` | line 89 (also `FlatEncoding/Tests.lean:103`) | 1.0.0 | 3.5 KB |
  | `nonce-list-v3.cbor.hex` | line 94 | 1.1.0 | 254 B |
  | `minting-policy-v3.cbor.hex` | line 99, trace messages renamed | 1.1.0 | 483 B |

- two functions on integers, with concrete calls and symbolic `Integer` cases:

  | file | origin | computes | concrete calls | proof budget |
  | --- | --- | --- | --- | --- |
  | `saturate.uplc` | the hand-written program of Lean-blaster's `Tests/Smt/Benchmarks/UPLC/Examples/Integer/Saturate.lean` (commit `49a4886`), ported to textual UPLC | x·(x+1), by a loop adding 2n for n from x down to 1 | 100, 256 (7260 and 18492 steps) | 7100 steps |
  | `fibonacci-naive.cbor.hex`, `fibonacci-size.cbor.hex` | CardanoLedgerApiBlaster's `Tests/Functions/Fibonacci`, the files this repository removed in `ddaf2d2` | Fibonacci numbers, naively and optimized for size | 10, 15 (about 8k and 90k steps) | 4000 steps |

The driver warns about script files (`*.uplc`, `*.flat`, `*.cbor`, `*.hex`) that `repoScripts`
does not list, and benchmarks them with format `auto`.

A symbolic case applies a script to the free arguments given by its `symbolic?` in
`repoScripts`. The functions take one `Integer`. For a validator, the number of `Data`
arguments is the least number of `Data.I 0` arguments with which the script, evaluated
natively, no longer returns a lambda:

- 3 for test3–test7, test9 and `aiken-validator-v1`;
- 2 for test8, `nonce-list-v3` and `minting-policy-v3` (parameterized V3 scripts).

The functions' symbolic cases also run at the `proofSteps` budget of the proof they come from:
the Lean-blaster `saturate` proof (7100 steps) and CardanoLedgerApiBlaster's Fibonacci proofs
(4000 steps).

The cost varies widely. At 2000 steps:

- nonce-list-v3 takes 0.2 s, test9 0.3 s, test4 1.4 s, test8 4.8 s and test3 20 s;
- test6 takes 144 s and 2.3 GB;
- aiken-validator-v1 takes 574 s and 6.3 GB, only to reduce to `State.Error`;
- minting-policy-v3 exceeds the 600 s timeout;
- saturate takes 0.3 s, and the Fibonacci functions 1.4 s.

At their proof budgets, saturate takes 0.6 s and unrolls to a 20k-object term, and the Fibonacci
functions take 5.6 s. The two Fibonacci implementations optimize to the same term (same
`prop_hash`), which is what CardanoLedgerApiBlaster's equivalence proof of them relies on.

A budget too small to get past a validator's prelude reduces to a mere `State.Error`: test8
does so at up to 1000 steps.

## How a run works

1. The driver writes one case file per case under `PrepUplc/Generated/`. This directory is
   rewritten on every run and not committed. A single case can be rerun by hand with
   `lake lean <case-file>`, which prints its measurement.
2. It runs `lake build Benchmark`. The library root imports everything the cases import, so the
   cases never build anything themselves.
3. It gets each case's module setup from `lake setup-file` and starts `lean --setup … <case-file>`
   directly. This is the setup `lake lean` would use, so the precompiled PlutusCore and Blaster
   libraries are loaded and `#prep_uplc` runs native code, as in `lake build`. The driver keeps the
   process id to watch memory and to stop the case after `--timeout` or above `--max-rss-mb`.
4. Each case runs in its own process, so a crash stays contained and each peak is its own.

A run directory, by default `Benchmark/results/<time>-<commit>[-<label>]` (not committed),
holds:

- `meta.json`: machine, Lean, PlutusCore and Blaster revisions (a checkout with local changes shows
  as `-dirty`), the plutus revision of the conformance tests, and the options;
- `results.jsonl`, `results.csv`: one record per case;
- `summary.md`: status counts, totals, machine steps per second (over the closed programs of at
  least 1000 steps, and for the 10 programs with the most steps), slowest and most memory-hungry
  cases, conformance by category, native run times, closed programs that were not fully
  evaluated, and failures;
- `logs/`, `raw/`: each case's `lean` output and harness measurement.

`results.jsonl` grows as cases finish. `--resume <run-dir>` continues an interrupted run (cases
recorded as `crash` or `no_result` run again), and `report <run-dir>` rewrites its CSV and
summary.

## Comparing runs

```sh
make bench_prep_uplc BENCH_ARGS="--label before"
# change Blaster or PlutusCore, then:
make bench_prep_uplc BENCH_ARGS="--label after"
make bench_prep_uplc_compare BASE=Benchmark/results/<…-before> NEW=Benchmark/results/<…-after>
```

To try another Blaster revision, point `require Blaster` in `lakefile.lean` at it and run
`lake update Blaster` before the second run. A change to PlutusCore itself needs nothing more:
the driver's `lake build Benchmark` rebuilds the changed modules and `libPlutusCore.so`.

`compare` reports the following, with ratios given as new / base:

- the geometric mean of the `#prep_uplc` time, peak-memory and steps-per-second ratios per suite,
  over the cases that succeeded in both runs;
- the geometric mean of the native time and steps-per-second ratios, over the closed programs run
  in both. For steps per second, above 1 is faster. When a machine change alters the step counts,
  these ratios say whether the steps themselves got cheaper;
- the cases whose `#prep_uplc` time or native time changed by more than `--threshold` percent
  (default 10). Cases under `--min-ms` (default 20) or, for native times, `--min-native-us`
  (default 100) in both runs are left out;
- status changes, and cases found in only one of the runs;
- cases whose native result or step count changed;
- cases whose optimized term changed, by `prop_hash` (by head and size against runs made before
  the hash existed).

### Changing the CEK machine

Every case runs `cekExecuteProgram`, and with it `runSteps` and `step`, twice: symbolically
through `#prep_uplc`, and compiled in the native run. So a change to
`PlutusCore/UPLC/CekMachine.lean` shows up in both times. It also shows in the native results
and step counts, and in the optimized terms. For example, starting every program as
`force (delay t)` adds 3 steps to each closed program: `compare` lists all 33 in a small run
under native changes, while no optimized term changes, since no result does.

Things to keep in mind:

- **Fixed step budgets.** Closed programs run to completion, so they stay comparable when steps
  get finer or coarser. Symbolic cases stop after `--symbolic-steps` steps, so if a step does
  more or less work, they cover a different part of the validator and their numbers don't
  compare.
- **Small programs.** Most conformance programs are tiny, and their `#prep_uplc` time is mostly
  the fixed cost. Machine changes show mainly in `example/*`, the heavy builtins and the
  symbolic cases: `--filter example/` or `--suite repo,symbolic` narrows a run to them.
- **Correctness.** This is not a correctness check: changed native results, step counts or
  optimized terms point at a semantic change, but the conformance tests are what show whether
  the machine is right.
- **The machine's API.** The harness calls `cekExecuteProgram`, `step`, `initialState`,
  `applyParams`, and matches `State.Halt` and `State.Error` (`runNative`, `countSteps` and
  `nativeRun?` in `PrepUplc/Harness.lean`). Renaming or re-typing those means adapting these
  three functions.

## Running on GitHub

The `ci-benchmark` workflow (`.github/workflows/ci-benchmark.yaml`) runs the suite on a
GitHub runner. A maintainer (repository owner, organization member or collaborator) triggers it
with a PR comment whose first line is

```
/run-benchmark [<plutus-ref>] [<option>...]
```

for example `/run-benchmark`, `/run-benchmark --suite repo,symbolic` or
`/run-benchmark 1.64.0.0 --filter example/ --runs 3`. It can also be run by hand from the
Actions tab, with the same two inputs.

- **Code:** the run benchmarks the PR head as of when it starts, which can be newer than the
  commit reviewed when the comment was posted; the PR comment names the commit. The job that runs
  the PR's code has a read-only token and keeps no credentials. Only the jobs that never run it
  can write to the PR.
- **Conformance programs:** it checks out IntersectMBO/plutus at `<plutus-ref>` (default
  `master`) and regenerates the conformance tests from it, so the conformance cases match that
  checkout. The checkout is only read as data. The driver takes only the ledger languages and
  formats `#import_uplc` accepts from the generated tests, and skips any other test with a warning.
- **Options:** only `--suite`, `--filter`, `--exclude`, `--max-steps`, `--symbolic-steps`,
  `--timeout`, `--max-rss-mb`, `--runs` and `--jobs` are accepted, each with a value of plain
  characters.
- **Defaults:** the runner's size sets them: half its cores as parallel cases, its memory (less
  2 GB) shared among them, and `--timeout 300`. Options given in the comment override them.

Where the results go:

- **Summary page:** the workflow run's summary page shows the whole `summary.md`.
- **Artifact:** the artifact `prep-uplc-benchmark-<run-id>` holds the whole run directory. Once
  downloaded and unzipped, it works locally with `report` and `compare` like any other run.
- **The PR:** a comment-triggered run posts a comment with the status, time and native-time
  tables and links to the rest. It also reports a `benchmark` check on the PR head.

GitHub's runners are shared and vary from run to run. Compare their timings with care; status
changes, native results and optimized-term changes are exact.

## Noise

- Parallel cases (`JOBS`, `-j`) compete for memory bandwidth and caches. Use them for quick
  looks, and compare runs made with the same `-j`. Two identical `-j 4` runs differed by up to
  13% on single ~200 ms cases, with a geometric mean ratio of 1.05.
- A cold `#prep_uplc` costs about 0.2 s even on a 10-step program, so for the small conformance
  programs this fixed cost is most of what is measured.
- The first `#prep_uplc` of a process pays one-time costs. `--runs N` repeats it on fresh copies
  of the environment and reports the best and median times. `peak_delta_kb` is the largest
  increase over the runs, and later runs reuse memory the first one touched.

## Writing a benchmark by hand

The harness commands also work in any file that imports `Benchmark.PrepUplc.Harness`, several
per file:

```lean
#bench_prep_uplc "<id>" <PlutusScript-or-Program constant> [<conversion-fn>] <max-steps>
#bench_prep_uplc_file "<id>" <PlutusV1|PlutusV2|PlutusV3> <format|auto> "<path>" [<conversion-fn>] <max-steps>
set_option bench.prepUplc.runs 5   -- before the command
```

A conversion function that takes no arguments, such as
`def benchArgs : List PlutusCore.UPLC.Term.Term := [.Const (.Integer 100)]`, makes a concrete call:
the case is closed, so the harness also runs it natively.

The measurement is printed as an info message. It is also appended as a JSON line to the file
named by the environment variable `PREP_UPLC_BENCH_OUT`, if set.

To add a script to the suite, list it in `repoScripts`. A Lean constant's module must also be
imported by `Benchmark.lean`. Set `symbolic?` for symbolic cases, `proofSteps` for the budgets of
its proof, and `applied` for concrete calls.
