# Reusable CEK optimization rules on Blaster PR #472

Enable the new rules with:

```lean
import PlutusCore.UPLC.Optimize.Extension
```

The existing `#prep_uplc` interface is unchanged. This module does **not** import
the old Aiken fixture-specific extension. It recognizes supported structural
patterns in CEK states, infers their capture positions, checks the required
builtin bindings, and instantiates kernel-checked summary theorems.

Blaster remains pinned to PR #472 revision
`fe7a8fbe001594d8275ebb1783af8dea305f2bdd`.

## Shared rules

| Module | Reusable responsibility |
| --- | --- |
| `Optimize/Plan.lean` | Exact return/error costs, arbitrary continuation boundaries, finite-fuel execution, and composition |
| `Optimize/ListTraversal.lean` | One shared induction for reconstructing traversals; one for short-circuit searches |
| `Optimize/Administrative.lean` | Lambda application/entry, force-delay blocks, environment lookup, and terminal returns |
| `Optimize/Prefix.lean` | Definitional certificates for bounded administrative-block fusion, including symbolic remaining fuel |
| `Optimize/Composition.lean` | Compose identity, constant-return and Boolean-assertion consumers; discharge the empty continuation and terminal conditional |
| `Optimize/ScalarSearch.lean` | Six scalar predicate instances of the search scheme, with arbitrary needles and capture layouts |
| `Optimize/ByteTraversal.lean` | Checked byte-list reconstruction with a parameterized length relation, bound and capture layout |
| `Optimize/Extension.lean` | Structural recognition, builtin-binding certificates and PR472 registrations |

There is no beneficiary, Cardano context field, script purpose, 28-byte
requirement, or fixed environment offset in the new extension's rules.
The byte traversal supports `bound = length`, `bound < length` and
`bound ≤ length`; operand order is preserved from the compiled code.
The search supports integer/byte-string equality and ordering comparisons.

The original Aiken experiment now also uses the shared traversal induction.
Its old public API and opt-in matcher remain for comparison; the generic
extension does not depend on them.

The traversal execution rule preserves its known returned-value shape. This
matters when continuing after decoding: replacing that value by an arbitrary
`CekValue` would prevent recognition of the following list operation.
Administrative-block fusion then crosses the fixed intervening CEK steps.
It carries a definitional execution certificate, stops at supported control
boundaries, refuses cycles and unfinished blocks longer than 32 transitions,
and does not execute saturated builtins.

## Certificate boundary

A traversal adapter supplies certificates for the empty case, one successful
iteration, one reconstruction step, and rejection. A search adapter supplies
empty, match, tail and rejection blocks. The shared theorem handles arbitrary
lists, continuations and fuel. Additional element operations can reuse that
theorem by supplying new bounded certificates instead of another list induction.

Capture positions are inferred from the code. A `Bindings` value contains
proofs of the required environment lookups. The recognizer checks the complete
closed code skeleton and the self-closure's captured environment; extracting
a predicate from part of the code is not sufficient to authorize a rewrite.
Only closed code/builtin values use definitional equality. Unknown symbolic
captures and trailing environments are carried structurally; metavariables
are conservatively rejected. Unsupported shapes retain ordinary evaluation.

These are deterministic optimizations with kernel-checked theorems. They do
not use AI, Horn clauses, new axioms or assumptions that decoding succeeds.

## Preserved behavior

- Failed element decoding, failed checks and insufficient fuel remain distinct.
- Searches stop at the first match; a malformed later element is not visited.
- Checked reconstruction visits the entire list. A later malformed element
  still rejects even when an earlier element would satisfy a later search.
- Reconstruction costs are charged only when unwinding actually occurs.
- Continuation costs are charged only if the producer returns successfully.
- The budget is **CEK transitions**, not ledger CPU/memory `ExBudget` units.

The search uses 16 transitions for the empty case, 47 to return on a match,
60 to reach the next tail, and 31 to reject a wrong element type. Returning
to an empty continuation takes one additional transition to halt. These
numbers are established by the bounded CEK certificates, not inferred from
benchmark timings.

## Validation

`Tests/UPLC/Optimize/Generic.lean` checks:

- Six search predicates and two independently arranged capture layouts.
- Byte traversals at bounds 28 and 32, plus both ordering relations and
  different layouts, without adding new registered rules.
- Arbitrary unused captures/trailing context disappear from residuals.
- Rejection of wrong builtin bindings, decoder mismatches and changed recursion.
- Exact fuel boundaries, malformed data, short-circuiting and continuation costs.
- Literal occurrence of both supported skeletons in the independently
  Aiken-compiled spending validator.
- Theorems' transitive axioms contain only `propext`, `Quot.sound` and
  `Classical.choice`; neither `sorryAx` nor `blasterProven` is admitted.
- A deliberately false search property produces `n = 7`, replayed against
  the original CEK evaluator. The same diagnostic works after full-program
  preparation. A false claim that the eager Cardano validator never succeeds
  produces the fixed beneficiary byte string; its acceptance is replayed
  through the original full CEK execution. These are singleton diagnostics,
  not a claim of arbitrary-list model extraction.
- Full preparation at fuel 100,000 retains 137, 133, 179 and 303 nodes for
  integer membership, byte-string membership, threshold assertion and the
  eager Cardano fixture, respectively. Each residual is checked to contain
  no `runSteps`, `runStepsPreservingState` or `step` call. The eager residual
  must contain both generic traversal and search summaries.

Isolated symbolic searches retain 136–143 distinct expression nodes at fuel
1,000, 10,000 and 100,000 across three predicates and three continuations.
Checked byte traversals retain 97–99 nodes at all three budgets. The old
Aiken compatibility wrapper retains 113 nodes after the shared-proof refactor;
the original specialized implementation retained 58 at commit `77d7fa2`.
The added abstraction has fixed overhead, rather than expansion with fuel.

The existing cost-budget runner's unrelated termination `sorry` is outside
these proofs' dependencies.

```sh
lake build Tests.UPLC.Optimize.Generic Tests.UPLC.Optimize.AikenValidation \
  Tests.UPLC.CekMachine.Tests Tests.UPLC.PreProcess.Tests
```

## Full-program measurements

`bench.py` starts from complete programs through `#prep_uplc`, rather than
injecting a loop-entry state. The cases are three UPLC programs (integer
membership, byte-string membership, and an integer threshold with an assertion
consumer) and the independently Aiken-compiled eager spending validator.

`results.json` records completed runs, timeouts, residual node counts,
summary presence and remaining evaluator calls. A non-baseline run retaining
the evaluator is marked `residual_evaluator`, not counted as an optimization
success. Baseline imports no optimization extension; generic imports
only the new shared extension. `combined` additionally imports the old adapter
and is available for optional comparisons.

| Complete program | Generic nodes at 1k / 10k / 100k fuel | Baseline at 100k | Generic at 100k |
| --- | --- | --- | --- |
| Integer membership | 137 / 137 / 137 | 20 s timeout | 1.67 s |
| Byte-string membership | 133 / 133 / 133 | 20 s timeout | 1.77 s |
| Integer threshold / assertion | 179 / 179 / 179 | 20 s timeout | 1.77 s |
| Aiken eager spending validator | 303 / 303 / 303 | 20 s timeout | 2.33 s |

All twelve generic runs completed with no residual evaluator call.

Each warm child uses one Lean worker, a 3 GiB virtual-address cap and a
20-second wall deadline in the recorded run. Wall times include Lake startup,
imports and elaboration. They are single development runs with native C
modules built using an `-O0` compiler wrapper; they are not release benchmarks.
Residual size and successful completion are the primary evidence.

```sh
python3 experiments/generic-optimizations/bench.py \
  --budgets 1000 10000 100000 --modes baseline generic --timeout 20
```

## Scope

Recognition supports the stated recursion/continuation skeletons and scalar
operations. Different recursion encodings, captured dynamic predicates,
arbitrary folds, trees and other decoder shapes need further adapters or
normalization rules. The shared certificate interfaces are in place; automatic
discovery of arbitrary UPLC summaries is not implemented.

The Cardano fixture quantifies over raw signatory elements while fixing the
surrounding context shape. It does not establish compact preparation for a
universally quantified raw `ScriptContext`.

Compact preparation and exact equivalence do not by themselves provide
automatic induction or guarantee that SMT proves every property of a summary.
