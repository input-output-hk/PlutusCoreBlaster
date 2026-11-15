# Aiken validation traversal on Blaster PR #472

This opt-in experiment proves and registers an exact summary of a real
Aiken-compiled UPLC validation/reconstruction loop. It uses ordinary Blaster
optimization and SMT solving, without Horn clauses or new axioms.

**Result:** the isolated traversal leaves 58 distinct residual expression nodes
at CEK fuel 1,000, 10,000 and 100,000. The false diagnostic property still
produces an SMT counterexample, replayed through the original CEK machine.
**Limit:** full-validator `#prep_uplc` did not improve within the measured
30-second deadline. This is a working loop-summary experiment, not a completed
solution to arbitrary-context preparation or a production speedup claim.

## Revisions and fixture

- PlutusCoreBlaster base: `79fce4ac2c74d376c2576edab19a9ba2e7dd5c1b`.
- Blaster: PR #472, pinned to `fe7a8fbe001594d8275ebb1783af8dea305f2bdd`.
- Aiken: `v1.1.24+bacbeb3`, stdlib `v3.0.0`, UPLC 1.1.0 / Plutus V3.
- `provenance.json` pins the readable compiler artifact's SHA-256.

The fixture deliberately validates every signer's 28-byte length and
reconstructs the list before checking beneficiary membership. It represents
an eager traversal; Aiken's minimal `list.has(tx.extra_signatories, beneficiary)`
validator does not itself perform that eager prepass. Context fixtures are
synthetic shape tests, not ledger-valid transactions.

`ValidationCode.lean` contains the literal loop body from the compiler output.
The test checks that this body is a subterm of the complete compiled fixture.
Aiken source-level names are neither present nor matched at the UPLC boundary.

## Proof and rule

- `PlutusCore/UPLC/Optimize/RunSteps.lean`: fuel-prefix composition lemmas.
- `PlutusCore/UPLC/Optimize/Aiken/Validation.lean`: checked CEK blocks, a compact
  validation plan, and the universal finite-fuel equivalence theorem.
- `PlutusCore/UPLC/Optimize/Aiken/Extension.lean`: PR472 registration and matcher.
- `Tests/UPLC/Optimize/AikenValidation.lean`: proof audits, recognizer rejection
  checks, symbolic residual-size checks and counterexample/replay tests.

The theorem quantifies over arbitrary encoded lists, fuel, surrounding stack,
unused captures and the trailing environment. Required builtin captures and
code are fixed by the recognized fragment. No input-validity premise is
silently assumed. The plan preserves all outcomes:

| Path | CEK transitions before returning/failing |
|---|---:|
| Valid list of length n, return the identical encoded list | 16 + 81n |
| First non-byte element after k valid elements, error | 80k + 27 |
| First wrong-length byte string after k valid elements, error | 80k + 56 |

Fuel before termination exhausts. Successful validation resumes the original
continuation with the correct remaining fuel. Pending reconstruction frames
are accounted for; they are not treated as zero-cost work.

The proof audit allows only `propext`, `Quot.sound` and `Classical.choice`.
Neither `sorryAx` nor `Blaster.Tactic.blasterProven` occurs in the summary or
registered theorem. The upstream, unused cost-budget runner's existing
termination `sorry` is outside these proofs' transitive dependencies.

The dispatcher structurally checks symbolic inputs and repeated captures. It
uses definitional equality only on closed code/builtin constants, and rejects
expression/universe metavariables. This avoids treating unknowns as constraints
that can be assigned, and avoids the optimizer's separate local-context model.
Wrong loop bodies and builtin aliases are tested to reject.

A small generated PR472 theorem matcher is invoked after recognition. A giant
literal-pattern theorem was attempted first, but rule compilation was too slow.
No Blaster source changes are required by the final implementation.

## Solver and counterexample behavior

The replacement is optimized normally, producing a compact recursive plan that
ordinary SMT translation understands. Simply using `noRestart := true` kept
preparation compact but left an unprocessed nonrecursive helper that SMT
translation rejected, so that variant is not the shipped rule.

The deliberately false claim says the decoder can reject a singleton integer
only when that integer is negative. Blaster reports `n = 0`; a kernel-reduced
replay establishes that the original CEK traversal rejects `[Data.I 0]`.
This is a small malformed-input diagnostic, not a counterexample to the actual
beneficiary requirement or a demonstration of general list-model extraction.

## Full-validator measurements

Both configurations use the same pinned PR472 engine; the only difference is
importing the optional extension. `bench.py` prepares the complete eager
validator on an arbitrary `List Data` in the signatory field.

| CEK fuel | Without rules | With rules |
|---|---|---|
| 1,000 | 324 residual nodes; completed | 30 s timeout |
| 10,000 | 30 s timeout | 30 s timeout |
| 100,000 | 30 s timeout | 30 s timeout |

See `results.json` for the observations. Each child has a 3 GiB virtual-address
cap, one Lean worker and a 30-second wall deadline. Timings include imports and
elaboration, are single runs, and are not release benchmarks. Local bootstrap
used a faster C-compilation configuration for some native dependency modules;
expression counts and kernel proofs are the primary evidence.

The isolated validation-loop result does not establish an end-to-end win.
The remaining membership search and continuation normalization are next
investigation targets; the timeout runs do not isolate which dominates.

## Use and reproduce

With Lean/Lake 4.24.0 and Z3 >= 5.4.0 available:

```sh
lake update
lake build Tests.UPLC.Optimize.AikenValidation \
  Tests.UPLC.CekMachine.Tests Tests.UPLC.PreProcess.Tests
python3 experiments/aiken-validation/bench.py --timeout 30
```

To activate the rules in an application:

```lean
import PlutusCore.UPLC.Optimize.Aiken.Extension
```

Ordinary PlutusCore imports do not activate the experiment. The test is included
in the root `Tests` target. Recompile the Aiken fixture from this directory with
`aiken build --uplc`; the tracked `eager_beneficiary.uplc` is the original output.
The matcher currently supports this exact compiled body and capture layout.
Compiler variants and other decoder shapes are not claimed supported.
