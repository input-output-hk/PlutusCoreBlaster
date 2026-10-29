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
shared CI runners are not performance comparisons.

For reproducible Docker builds, the integration must pin PlutusCoreBlaster, Lean and Lean-blaster
to exact revisions. The upstream benchmark currently also requires a stable release and a
released downstream user for a ranked entry. This executable and gate establish technical
compatibility; they do not establish eligibility for the ranking.
