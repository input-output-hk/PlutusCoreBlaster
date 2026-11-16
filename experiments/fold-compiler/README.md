# Proof-producing fold compiler experiment

Pinned baseline: PlutusCoreBlaster `240891f8566802ceece22066c8beb7cbda173500`,
lean-blaster PR472 `fe7a8fbe001594d8275ebb1783af8dea305f2bdd`, Lean 4.24.0.
This is an opt-in prototype (`import PlutusCore.UPLC.Optimize.FoldExtension`).
The default optimizer and the PR93 branch are unchanged.

## Verified results

`Smoke.lean` compiles an integer sum over raw Data and an integer sum over
key/value pairs. Each generated callback certificate is kernel checked. A
callback that reads the list tail is declined. The shared unbounded fold
correctness theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

`results.jsonl` records the final integration run, with fuel 10000:

| Compiled Aiken validator | Output nodes | General CEK remains | Closed definition checked by kernel |
|---|---:|---|---|
| withdrawals_sum | 347 | no | yes |
| proposals_deposit | 370 | no | yes |

These are **preparation/optimization results**, not proofs of the validators'
business properties. The previous corpus property-proof count is unchanged.
No ledger `isValidContext` implementation or coverage proof has been added.
The benchmark checks closure and submits the optimized function as a safe
Lean definition to the kernel; absence of CEK constants alone is insufficient.
Wall timings are diagnostic (development native dependencies built at O0),
not a controlled speed comparison.

## Mechanism and current scope

1. Recognize and check the entire recursive Aiken fold spine, including the
   recursive closure and the captured chooseList/tailList builtins.
2. Generate scalar Lean code for the callback. The candidate evaluator has a
   96-transition compilation limit **per callback**, not a list-length bound.
3. Certify the emitted code against the original CEK callback for every tail
   and continuation, including malformed Data and exact failure costs.
4. Instantiate the existing generic fold induction and kernel-check the exact
   source-to-summary equality. Hash-cons the returned optimizer expression.

The spine proof is shared; callbacks are generated from code, not selected by
field name or by a catalogue of sum predicates. Unused captured values are
abstracted during certification and the proof is instantiated at their exact
original values. Callback synthesis sees only the target's dependencies, and
the data program must not depend on ambient proof variables. Kernel checks
run synchronously and reject axioms beyond the three standard Lean axioms.

Current support is one recursive Aiken spine, integer accumulators/results,
and Data or PairData lists. Tail-dependent/recursive callbacks are outside
this leaf compiler. A missing candidate or certificate leaves the original
interpreter in place; it is never interpreted as a runtime error.
Nested-fold composition, other compiler spines, other accumulator types and
arithmetic/property automation over the resulting fold remain open.

## Conditional-token example: unresolved

`../context-corpus/lib/fold_examples.ak` exports an independent function that
sums quantities iff the key equals a symbolic asset. `sum-if-asset.hex` is the
Aiken v1.1.24 export from:

```sh
aiken export --module fold_examples --name sum_if_asset experiments/context-corpus
```

The strengthened `Conditional.lean` test did not finish within 50 seconds.
This case is **not counted as passing**. Early small-node results were discarded:
they did not enforce export closure, and ambient optimizer hypotheses could
produce a proof-dependent candidate. The final compiler isolates dependencies
and rejects ambient proof dependencies. Do not infer conditional/nested-fold
support from the two passing sum validators.

## Reproduce

Run from the repository root, with the pinned Lean toolchain available:

```sh
lake build PlutusCore.UPLC.Optimize.FoldExtension:dynlib
lake lean experiments/fold-compiler/Smoke.lean
python3 experiments/fold-compiler/bench.py --cases withdrawals_sum proposals_deposit --engines fold --fuel 10000 --timeout 45
lake lean experiments/fold-compiler/Prep.lean
# Known incomplete conditional example:
timeout 50 lake lean experiments/fold-compiler/Conditional.lean
```

The benchmark reuses the checked-in Aiken corpus artifacts; it does not require
recompiling them. `Prep.lean` additionally exercises the actual `#prep_uplc`
command and its environment rollback boundary on both validators.
