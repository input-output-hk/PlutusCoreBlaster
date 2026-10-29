# Native CEK benchmark

`bench_cek` is a compiled Lean executable for the
[Plutus VM Benchmark image contract](https://github.com/lantr-io/plutus-vm-benchmark/blob/main/docs/IMAGE_CONTRACT.md).
It calls the Flat decoder and `cekExecuteProgramWithCost` directly. Build with:

```sh
lake build bench_cek
python3 scripts/test_bench_cek.py
```

## Evaluation parameters

Every evaluation uses builtin semantics variant E and the library's compiled-in variant E cost
model (`PlutusCore/UPLC/CostModels.lean`): PlutusV3 at protocol version 11. The program is already
fully applied, so the runner supplies no arguments. Counting includes startup cost. The runner
accepts any CEK result, including a non-unit value; it does not apply the ledger's CIP-117 unit
result rule. The correctness gate compares evaluation status and both ExUnits with Haskell.

The default fuel is 100,000,000 CEK steps. A run must end in `Halt` or `Error`; reaching the fuel
limit exits 1 without a check or timing row. Increase `MAX_STEPS` if necessary. The fuel is a
safety limit, not an execution budget.

## CLI and output

```sh
.lake/build/bin/bench_cek check /path/to/script.flat [MAX_STEPS]
.lake/build/bin/bench_cek time /path/to/script.flat d3,eval 5000 [MAX_STEPS]
.lake/build/bin/bench_cek profile /path/to/script.flat [RUNS] [MAX_STEPS]
```

`check` writes one headerless CSV row to stdout:

```text
vm,script,status,cpu,mem
```

The VM identifier is `plutuscore-lean`. `script` is the filename without its extension. `status`
is `ok` for `Halt`, `error` for a CEK evaluation error. Decode failures, missing files and fuel
exhaustion exit 1 and write `EVAL_FAIL:` to stderr. Invalid CLI arguments exit 2.

`time` takes a comma list of `d3` and `eval`, and a positive measurement duration in milliseconds.
It runs D3 before eval when both are selected. Before each loop it writes
`PVB_LOOP <loop> <script>`. After it finishes, it writes `PVB_RESULT <loop> <csv-row>` with schema:

```text
vm,script,mean_ns,median_ns,min_ns,max_ns,stddev_ns,iterations
```

File I/O, process startup and the initial evaluation are outside timing. The initial evaluation
must succeed. A process runs the selected loops for one script:

- **D3:** convert raw bytes into the decoder's byte-string representation, Flat decode, and
  costed evaluation on each iteration. There is no decoded-program cache.
- **Eval:** decode once before timing, then costed evaluation on every iteration.

Both operations use non-inlined IO boundaries. Every iteration has fresh evaluation state and
cost accounting. Its success status and both costs must equal the initial evaluation, checked
after stopping the timer. Each loop has five warm-up iterations, then at least 50 measured
iterations and at least the requested total time in the measured operations. There is no sample
cap or outlier removal. Statistics use individual iteration times, a sample standard deviation
and the average of the two middle samples for an even-sized median. Derived statistics are
rounded to integer nanoseconds when written, as the upstream report requires. CSV names are escaped.

## Compiler replacements

Kernel-checked `@[csimp]` equalities select two runtime implementations:

- CBOR scalar decoding keeps the unconsumed `List Char` suffix instead of copying
  it through `String` at every integer or bytestring leaf. The equivalence proofs
  include rejected inputs, bignums and indefinite bytestrings.
- `runStepsWithCost` compiles to an eager costing loop. It selects the machine
  costs once and charges builtin calls before executing them, without retaining
  a call history. Its equality preserves the complete state and both ExUnits for
  every semantics variant, initial state and fuel limit, including failed builtins.

The logical costing and CEK definitions remain available to Blaster and the
existing proofs. These compiler replacements use neither `sorry` nor `native_decide`.

## Diagnostic profiling

`profile` writes one JSON object (schema version 1), with ten measured runs by default. It is
independent of `check` and `time`: the normal evaluator and benchmark timers contain no profiling
hooks. File I/O, warm-up, validation and JSON serialization are outside the reported durations.
Every profiled run checks the decoded program, **complete final CEK state** and both ExUnits
against the uninstrumented evaluator. CEK errors can be profiled; malformed Flat or exhausted
fuel exits 1 without JSON.

For a readable report and saved raw data:

```sh
python3 scripts/profile_bench_cek.py /path/to/script.flat --runs 20
python3 scripts/profile_bench_cek.py /path/to/plutus_use_cases --runs 10
```

Files or directories may be combined. Results go to ignored `Benchmark/results/profile/`
(`--output` overrides this): one JSON per script and `summary.md`. The summary records the source
revision, whether the tree has local changes, and the host platform.

JSON durations and counts are **totals across RUNS**; divide by `runs` for per-run values:

- `baseline.decode_ns`, `baseline.eval_ns`: uninstrumented operations in the same process.
  Baseline/profile order alternates each run to reduce order bias. Their ratios to profiled
  totals show measurement perturbation; use the existing `time` command for benchmark results.
- `decode`: bytes to the decoder's string representation, string to bits (including `String.data`),
  and Flat parsing (version, term, constants/CBOR, padding), plus their inclusive `total_ns`.
- `eval.machine_ns`: ordinary CEK transitions **including step costing**, timed in pure blocks
  between saturated builtin calls. `machine_steps` includes uncharged Return transitions.
- `eval.builtin_eval_ns`: saturated builtin transitions through the existing `step`, including
  argument dispatch and result construction. `builtins` splits this by builtin, with call counts.
- `eval.builtin_cost_ns`: time inside the existing cost model, split by builtin as `cost_ns`.
  Calls remain retained and charged in reverse execution order after CEK execution, as in the
  logical evaluator. The compiled evaluator instead uses the eager loop described above;
  the diagnostic loop retains its original structure, so its allocation costs and phase
  timings do not describe that eager loop. `cost_pass_ns` is inclusive: it also contains cost
  accumulation, per-call clocks, statistics and loop overhead. Do not add it to `builtin_cost_ns`.
- `eval.total_ns`: inclusive instrumented evaluation. The difference from machine + builtin
  execution + cost pass is profiler dispatch, call recording and other bookkeeping.

Times are raw monotonic nanoseconds, with **no overhead subtraction**. `clock_pair_median_ns`
and `clock_pair_p95_ns` summarize 101 adjacent clock pairs (the median can be zero on a coarse
clock). Cheap builtins may be near that floor; their tiny
timings and relative rankings are unreliable. Profiling changes allocation, reference counting
and cache behavior, and can substantially inflate cheap workloads. Interpret large hot spots
alongside the baseline ratio, then confirm any optimization with the uninstrumented benchmark.
The JSON `cpu`/`mem` fields are ledger ExUnits, never wall-clock time or process memory usage.

## Haskell gate

Clone the benchmark repository at an exact commit, then run:

```sh
git clone https://github.com/lantr-io/plutus-vm-benchmark.git /tmp/plutus-vm-benchmark
git -C /tmp/plutus-vm-benchmark checkout fc252e35531ba5b2d76c564869a1121c9edb6e2f
make check_cek_benchmark BENCHMARK_ROOT=/tmp/plutus-vm-benchmark
python3 /tmp/plutus-vm-benchmark/check/gate.py Benchmark/results/cek/plutuscore-lean-check.csv
```

The Python driver checks CLI regressions, then runs one process per reference script with a
120-second timeout. It rejects missing scripts, malformed rows, wrong names, wrong status or
different CPU/memory ExUnits. It writes the upstream-compatible check CSV even on failure.
Normal CI runs this gate over all 89 scripts from the pinned benchmark commit. Timings from
shared CI runners are not performance comparisons. CI also passes `--profile-corpus` to check
the instrumented evaluator's complete final state and ExUnits on every script; its raw profiles
are saved beside the check CSV in `profiles/`.

For reproducible Docker builds, the integration must pin PlutusCoreBlaster, Lean and Lean-blaster
to exact revisions. The upstream benchmark currently also requires a stable release and a
released downstream user for a ranked entry. This executable and gate establish technical
compatibility; they do not establish eligibility for the ranking.
