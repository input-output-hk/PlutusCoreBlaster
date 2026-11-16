# Generic ScriptContext experiments

The target is **`∀ ctx, isValidContext ctx → property ctx`**, with every field
free and collections of arbitrary length. A successful preparation run is not
a proof of that target. This branch adds experiments; the optimization rules
from PR93, at `1d13b91934e74a021497b5ba8ff9932d481a9839`, are unchanged.

## What was actually checked

- **New kernel proofs (16 November):** `CountTheorems.lean` proves the original
  Aiken-compiled inputs/outputs/certificates/proposals count validators for every
  finite fuel and arbitrary-length lists. Every outer transaction field,
  redeemer, datum option and spending reference stays free. One length induction
  and two generic consumers are shared across the four programs. No SMT axiom
  or `sorry` is used. The exact result distinguishes acceptance, rejection and
  budget exhaustion; see the acceptance theorems below.
- 34 distinct validators compiled from independent Aiken source programs.
  They touch all 16 V3 transaction fields, the redeemer, spending datum and
  reference, and all six purpose constructors. Compiler and dependency pins
  are in `provenance.json`; source and compiled hashes are in `compiled.jsonl`.
- The official Aiken interpreter and the Lean CEK agree on all 34 programs
  on one independently Aiken-encoded stdlib placeholder: 12 accept, 22 reject.
  This is a concrete cross-interpreter diagnostic, not a ledger-valid fixture
  or a universal proof. `WireWitness.lean` additionally checks equality of
  the **entire** placeholder wire encoding in the Lean kernel.
- `Boundary.lean` proves the representation round trips and the transport
  of a universally quantified property under an explicit validity contract.
  No new axiom is used. The actual `isValidContext` definition is absent from
  this checkout; constructing its contract remains an obligation.
- `FeeProof.lean` passes `#blaster` for fee acceptance iff `fee ≤ 2000000`,
  at 1000 CEK steps, with all transaction fields and the spending payload free.
  `FeeKernel.lean` separately proves the same criterion directly for the
  original CEK executable, with only the standard Lean axioms. This strengthens
  the calibration without depending on SMT or preparation equivalence. Neither
  calibration supplies the full raw-context validity theorem for arbitrary
  purposes. The count cases now record conditional raw-context theorems;
  instantiation with a concrete ledger validity definition remains pending.

No list bound or fixed value for unrelated transaction fields is used in the
symbolic experiments. The concrete placeholder is used only for replay.

### Proven count properties

The kernel-checked `inputs_acceptance`, `outputs_acceptance`,
`certificates_acceptance` and `proposals_acceptance` theorems establish:

| Compiled validator | Accepts iff | Exact last-live-state cost |
| --- | --- | --- |
| inputs_count | inputs.length ≤ 4 and cost < fuel | 234 + 37 × inputs.length |
| outputs_count | outputs.length ≤ 8 and cost < fuel | 242 + 37 × outputs.length |
| certificates_count | certificates.length ≤ 3 and cost < fuel | 254 + 37 × certificates.length |
| proposals_count | 0 < proposals.length and cost < fuel | 286 + 37 × proposals.length |

The length constraints are acceptance conditions, never restrictions on the
quantifier domain. `execution` proves all three outcomes for **every** fuel;
`eventually_accepts_iff` removes fuel by existentially quantifying a sufficient
budget. `valid_raw_acceptance` and `valid_raw_eventually_accepts` transport these
properties to `∀ ctx, isValidContext ctx → ...`, conditional on the validity
predicate's spending-encoding coverage proof. They do not assume execution
correctness to obtain that result, and do not claim to handle other purposes.

`Fold.lean` additionally proves a generic accumulator/short-circuit scheme,
including errors, exact costs and arbitrary continuations. Its Aiken sum/nested
fold adapters remain to be implemented. These proofs do not automatically
register new recognizers in `#prep_uplc`; the earlier benchmark matrix remains
an unchanged measurement of the old rule set.

## Coverage

| Field | Operations in independently compiled programs |
| --- | --- |
| inputs | length, search by reference, sum of lovelace |
| reference inputs | search with nested value lookup |
| outputs | length, address search, sum, asset lookup, inline datum/hash, reference script |
| fee | comparison; input/output conservation |
| mint | policy lookup, policy count, nested asset fold |
| certificates | length |
| withdrawals | sum and credential search |
| validity range | interval membership |
| extra signatories | membership; all hashes have length 28 |
| redeemers | search using Data equality |
| datums | hash lookup and comparison with redeemer |
| transaction id | byte equality |
| votes | outer count; search using inner count |
| proposal procedures | count; sum of deposits |
| current treasury amount | option and integer comparison |
| treasury donation | option and integer comparison |

This covers the top-level field surface, not every nested certificate,
governance constructor or ledger invariant. This first corpus uses Aiken only;
Plutus/Plutarch programs are still needed as compiler holdouts.

## Measured limitations of the current rules

`results.jsonl` contains the full 34 × 2 × 2 matrix. `raw` quantifies arbitrary
Data. `view` quantifies all 18 outer fields of ScriptContext, including the
redeemer and purpose, with nested payloads still raw. Neither asserts full
ledger validity. Each trial has an 8 second deadline, a 3 GiB address-space
limit and one Lean worker. Imports were built beforehand. These are development
builds using a local `LEAN_CC` override to compile native modules at O0;
timings are diagnostic, not release performance claims.

| Input | Rules | Preparation finishes at fuel 1000 | Timeout |
| --- | --- | ---: | ---: |
| raw | baseline | 25/34 | 9/34 |
| raw | PR93 generic | 25/34 | 9/34 |
| view | baseline | 25/34 | 9/34 |
| view | PR93 generic | 25/34 | 9/34 |

The nine timeouts are `inputs_sum`, `reference_inputs_find`, `outputs_sum`,
`outputs_asset`, `outputs_inline_datum`, `mint_fold`, `withdrawals_find`,
`votes_nested` and `value_conservation`, in all four configurations.

Only `signatories_find` hits the existing search summary. The other programs
do not hit a traversal/search summary. A small residual expression can still
be a finite unrolling with `BudgetExhausted` in its remaining branches; the
absence of a `runSteps` constant is not sufficient evidence of abstraction.
The recorded `nodes` counts distinct expression nodes, including shared nodes,
in the root expression only, not its dependency closure.

`scaling.jsonl` repeats eight representative cases at fuel 10000 in view mode:
`inputs_count`, `outputs_sum`, `outputs_asset`, `mint_quantity`, `mint_fold`,
`signatories_find`, `votes_nested`, `redeemer_fold`. Baseline times out on 8/8;
the generic extension finishes only `signatories_find` (7/8 timeouts). Its
summary has 256 root nodes at both 1000 and 10000. The baseline has 181 nodes
at 1000 but times out at 10000. Compactness across budgets matters more than
the smallest expression at one low budget.

`pilot.jsonl` also probes explicit outer-shape assumptions on `inputs_count`
and `fee_control`. This helps diagnose hypothesis plumbing, not coverage of
an actual `isValidContext` definition.

## The validity boundary

`View` fixes the **encoding shape**, never the field values. Its lists and
map entries are unbounded. `WellShaped` deliberately does not assert recursive
field typing, hash lengths, canonical Value maps, uniqueness/order or ledger
consistency. `ValidityContract` requires a proof of:

```lean
∀ d, isValidContext d → WellShaped d
```

The kernel-checked `transport` theorem then gives:

```lean
(∀ d, isValidContext d → P d) ↔
  (∀ v, isValidContext (encode v) → P (encode v))
```

Thus quantifying over a suitable view can cover every valid raw context;
it does not justify replacing the validity predicate by shape alone.
Recursive typed views need corresponding coverage/round-trip proofs.
Validator acceptance must never be smuggled into the validity predicate.

Preparation must also see hypotheses *before* it expands the CEK execution.
The pinned PR472 optimizer does not seed a proof parameter into its hypothesis
map just because it enters a lambda. `UnderAssumptions.lean` tests a small
generic entry point that opens the parameters, registers local propositions,
optimizes the body and rebinds every parameter. `BoundaryRules.lean` supplies
one conditional representation rule; `Probe.lean` checks that it fires there.
Simply placing an `isValidContext` hypothesis in a later `#blaster` goal
cannot retroactively change `#prep_uplc`.

Extracting a view from raw Data also expands into many projected matches in
this experiment. Directly quantifying the view and transporting the theorem
is the cleaner starting point until projection/codec normalization improves.

We attempted automatic typed context generation with the Aiken blueprint too.
The generated schema includes opaque Value/Dict wrappers, while the exported
placeholder has a raw `Map` at the mint position. The current blueprint import
also reports pattern-metavariable errors on the full schema. That route needs
its own wire-representation investigation; it is not a verified typed codec.

## Refactoring direction

The unit of reuse should be a **verified operation scheme**, with program
fragments and their proofs as parameters. Transaction field names should
appear only in schema/projection metadata and test programs.

| Shared layer | Required contract | Reuses across |
| --- | --- | --- |
| codecs and projections | encode/decode laws, coverage under validity, product/sum/list/option/map composition | every field and compiler frontend |
| preparation under assumptions | retain proof scope and expose validity consequences before unfolding | every validator |
| CEK block summaries | arbitrary continuation and captured environment, exact errors and step cost | administrative blocks and callbacks |
| traversal with state and stopping | callback summary, accumulator invariant, stopping condition and induction proof | `any`, `all`, lookup, length, folds, decoding |
| composition | invoke a certified callback/inner summary rather than expand its implementation | outputs containing values, nested votes, two traversals |
| property lemmas | relate summarized operations to specifications under domain invariants | membership, sums, conservation, map properties |

In particular, generalize the current finite catalogue of scalar predicates
to a callback carrying a certified summary. Use accumulator/state parameters
for folds and explicit stopping behavior for short-circuit searches. Compose
these summaries for nested structures. A sound recognizer may fail to certify
a compiled loop; adding a fallback recognizer must not add another semantic
proof per field or silently assume a callback correct.

This moves induction into reusable Lean theorems. SMT is then useful for the
remaining finite scalar obligations. Merely hiding a loop behind an opaque
recursive function does not let SMT prove arbitrary properties of its result.
There is no promise of complete automatic proof for arbitrary UPLC programs.
No AI or Horn-clause backend is required for this architecture.

Keep execution cost separate from validity. For an unbounded search, validity
alone does not imply acceptance within 1000 steps. Distinguish:

- safety: valid context + successful execution implies the specification;
- adequacy: valid context + specification implies success with sufficient fuel;
- fixed-fuel equivalence: include a proved cost condition.

Skipping an eager validation traversal under a validity hypothesis still has
to preserve its CEK cost in the summary. Counterexamples should be reconstructed
through the proven encoding and replayed in the original executable CEK;
budget exhaustion and malformed input must remain distinct outcomes.

Accept a new scheme only when it supports independently compiled cases across
several fields, remains compact as fuel increases, preserves errors and cost,
and passes a held-out program without another semantic theorem. Next priorities
from this corpus are accumulator folds, nested summary composition and certified
validity consequences/codecs, rather than additional signatory-specific rules.

## Reproduce

Use Lean 4.24.0, the pinned Blaster dependency, Z3, Aiken v1.1.24+bacbeb3 and
stdlib v3.0.0. From the repository root, with those executables on PATH:

```sh
lake build Blaster PlutusCore.UPLC.Optimize.Extension ContextCorpus.Native
python3 experiments/context-corpus/validate.py --compile --proofs
python3 experiments/context-corpus/validate.py --kernel-proofs
python3 experiments/context-corpus/run.py --modes raw view --fuel 1000 --timeout 8
python3 experiments/context-corpus/run.py --cases inputs_count outputs_sum outputs_asset mint_quantity mint_fold signatories_find votes_nested redeemer_fold --modes view --fuel 10000 --timeout 8 --output scaling.jsonl
python3 experiments/context-corpus/run.py --cases inputs_count fee_control --modes raw view assumed --fuel 1000 --timeout 8 --output pilot.jsonl
```

The first command regenerates compiled artifacts, the fixture and the proof
calibrations. Logs and generated Lean probes live in the ignored `.work/`.
Results are committed separately from the generated artifacts. `ContextCorpus`
is an optional Lean library and is not imported by the normal test target.
