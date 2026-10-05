# Verified fused CEK preparation

`StagedCek` fuses the CEK `step`/`runSteps` loop into two mutually recursive
functions, `eval` and `ret`. Their parameters expose the remaining fuel, stack,
environment, and current term or value separately. This lets a symbolic
optimizer unfold known control before normalizing every value carried by an
intermediate `State` constructor. Environment lookup returns only the selected
value. Every recursive call consumes exactly one reference CEK transition.

`StagedCekProofs.run_eq_runSteps` proves equality with `CekMachine.runSteps`
for **every state, fuel, and builtin semantics variant**. The induction includes
constructor field order, constructor and primitive case selection, builtin
argument tags, and the existing `Halt`/`Error` convention at zero fuel.
`StagedCekProofs.execute_eq` lifts the result to program execution with parameters.
Both proofs are checked by Lean's kernel and use only `propext`,
`Classical.choice`, and `Quot.sound`; neither uses `sorry` or `native_decide`.
The equality is relative to the reference interpreter in this repository,
including its existing semantics. Budget-aware execution is separate.

## Opt in

The existing `#prep_uplc` command uses the reference interpreter by default.
Set this option in the scope of a preparation command to use fusion:

```lean
set_option plutuscore.stagedCek true
#prep_uplc prepared myScript myInputConverter 1800
```

The generated `.exec` definition still calls the reference interpreter. Only
the expression sent to Blaster for `.prop` preparation uses `StagedCek.execute`.
The theorem certifies this interpreter replacement **before optimization**;
it does not add a kernel certificate for the subsequent Blaster normal form
or its solver verdicts.

The companion Lean-blaster specialization change enables control-first
unfolding using local annotations:

```lean
attribute [local blaster_specialize 2]
  PlutusCore.UPLC.StagedCek.eval PlutusCore.UPLC.StagedCek.ret
attribute [local blaster_specialize 1] PlutusCore.UPLC.StagedCek.lookupValue
```

Indices are one based and include implicit parameters. The first two labels
select fuel; the third selects the environment spine. These annotations
require a Lean-blaster revision that implements `blaster_specialize`. They are
kept out of the evaluator itself so it remains independently usable and the
kernel proof does not depend on that optimizer feature.

## Validation and performance

```sh
lake build PlutusCore.UPLC.StagedCekProofs PlutusCore.UPLC.PreProcess
lake build Tests.StagedCek
```

The proof file prints its axiom dependencies during the build. The focused test
also checks `#prep_uplc` option scoping and the generated executable definitions.
Cardano measurements and additional Blaster normalization regressions live in
the companion Lean-blaster benchmark harness. Compare preparation plus proof
time on identical scripts, inputs, fuel, solver limits, and optimizer revisions.
A rejecting theorem at a low fuel bound is insufficient evidence of useful
coverage: accepting witnesses must still reach their expected final values.

This complements the existing fuel-free iteration/composition PR #42; it does
not replace that API or change the reference `step` implementation. Fusion
removes interpreter overhead, but it does not by itself merge symbolic paths
or eliminate the growth in branch contexts on larger contracts.
