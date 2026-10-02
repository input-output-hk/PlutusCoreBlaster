# CI operation

`ci-linux` keeps the existing required `build` check. It checks the build-script
regressions, uses the repository's `lean-toolchain`, resolves Z3 master to a full commit SHA and builds that snapshot from source, and builds the library and tests. Checkouts keep
no GitHub credentials; execution jobs have `contents: read`. Actions and the elan
installer source are pinned. The workflow validation job uses a checksum-verified
actionlint 1.7.12. Its two exact schema exceptions cover `queue` and
`copilot-requests`, which that linter predates; all other schema errors fail.

`scripts/check_lean_project_compilation.sh <target> [source-dir] [excluded-subtree]`
builds the target plus every selected `.lean` module, including the barrel. New
files are therefore checked even before somebody adds their barrel import.
Cached builds are valid: the script does not parse Lake progress messages.
An excluded subtree also excludes its sibling barrel, but excludes no similarly
named siblings. An invalid/empty selection fails. A failed Lake command survives
`tee`. Logs remain in `.ci-results/build/<target>.log`; `build.log` is retained
for the existing manual conformance workflow.

Every run uploads logs and `environment.json`, including the actual source commit,
Lean/Lake/Z3 versions, architecture and resolved `lake-manifest.json` when available.
Artifacts last 14 days. CI evidence is ignored by Git. Dependency branch policies
are unchanged: these records identify the commits resolved for each run; they do
not turn moving dependency branches into a stable release baseline.

The daily nightly-Lean workflow builds both the library and tests with Z3 master. Failures leave a red build job, even if reporting succeeds. A separate reporter
executes no repository code. It creates one bot-owned issue per failure episode,
stays quiet during repeated failures, then comments once and closes that issue on
recovery. The marker `<!-- blaster-nightly-lean -->` identifies these issues;
older manually managed nightly issues are not closed automatically. A setup failure
is reported as a check failure, not assumed to be a Lean breaking change.

Local checks for the new infrastructure:

```sh
python3 scripts/ci/test_build_check.py
node scripts/ci/test_nightly_report.cjs
make check_all
```

The first two checks require Python 3 and Node.js, respectively; `make check_all`
requires this repository's Lean and Z3 master environment. CI runner timeouts bound
cost but are not performance thresholds. Preserve the existing required-check
rules until the new workflows have been observed on actual PRs.

## Result interpretation

Lean compilation, a solver's `Valid` response, an independent reference/finite
oracle and a reconstructed kernel-checked proof are distinct evidence. In
particular, passing Blaster tests do not by themselves certify proofs. Preserve
negative and unknown cases; never repair CI by weakening a specification, changing
expected results, adding `sorry`/axioms, or silently excluding a failing category.

## Next rollout stages

1. Merge and observe these CI foundations. Track missed failures, signal quality,
   run duration and artifact completeness.
2. Exercise exact-commit downstream compatibility and reproducible benchmark jobs.
   Schedule conformance only after PlutusCoreBlaster #50's separation of build/report
   privileges and generator hardening is merged. Retain a pinned corpus baseline
   alongside the rolling corpus; report generated, excluded, failed and passed cases.
3. Evaluate the Lean-blaster manual CI-advisor pilot on known failures. Record useful,
   unsupported and duplicate reports, maintainer correction time and AI cost.
4. Enable periodic advisory reporting only after that evaluation, then consider one
   bounded regression-test/specification contribution bot. Changes always go through
   reviewed PRs and the deterministic checks. Performance claims require fresh
   base/head runs on equal environments and a controlled runner.

These later stages are follow-up work, not silently enabled by this change.

## Z3 master policy

Every run resolves Z3 master to a full commit and builds exactly that snapshot.
`.ci-results/z3-source.json` records the source ref, commit and build mode;
`z3-build.log` records compiler/configuration output. `environment.json` includes
both this source metadata and the executable's version. A moving master baseline
is identified by its commit, never only by a release-like version string.

Set `Z3_COMMIT=<full-SHA>` to replay an earlier master snapshot exactly. This is
also how the ecosystem matrix shares one solver commit across both consumers.
`Z3_BUILD_JOBS` defaults to two to limit memory pressure; a failed build fails CI.
The compiler and system libraries come from ubuntu-24.04. No built-solver cache is
restored. Manual local source builds can run `bash scripts/ci/build-z3.sh`; add the
absolute directory recorded in `.ci-results/z3-bin-path.txt` to PATH afterwards.
