import PlutusCore.UPLC.CekMachine.DecidableEq
import PlutusCore.UPLC.CekMachine.StackIndependence
import Tests.UPLC.CekMachine.Tests

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Term (Const Program Term Version)

def addTerm : Term :=
  .Apply (.Apply (.Builtin .AddInteger) (.Const (.Integer 1))) (.Const (.Integer 2))

def addProgram : Program := Program.Program (Version.Version 1 1 0) addTerm

/-- With ten steps of fuel the program halts on `3`. -/
theorem addProgram_halts :
    cekExecuteProgramWithSemanticVariant testSemanticsVariant addProgram [] 10
      = State.Halt (CekValue.VCon (.Integer 3)) := by decide

/-- From every stack `s`, the run of `addTerm` is at `State.Return s` on `3` after fewer than
ten steps. -/
theorem addTerm_returns (s : Stack) :
    ∃ k < 10, stepN testSemanticsVariant (State.Eval s [] addTerm) k
      = State.Return s (CekValue.VCon (.Integer 3)) :=
  runSteps_stack_independent testSemanticsVariant [] addTerm s 10 _ addProgram_halts

def applyIdentity : Term := .Apply (.Lam (.Var 0)) (.Const (.Integer 3))

/-- From every stack `s`, the costed run of `applyIdentity` is at `State.Return s` on `3` after six
steps, with its four `Eval` steps charged. -/
theorem applyIdentity_cost (s : Stack) :
    runStepsWithCost testSemanticsVariant (State.Eval s [] applyIdentity) 6
      = (State.Return s (CekValue.VCon (.Integer 3)), testBudget 64000 400) :=
  runStepsWithCost_stack_independent testSemanticsVariant [] applyIdentity s 6 _ _ (by decide)

-- Under any stack, a lambda with any body `M` applied to `addTerm` evaluates `M` with `3` bound.
example (M : Term) (s : Stack) :
    ∃ k, stepN testSemanticsVariant (State.Eval s [] (.Apply (.Lam M) addTerm)) k
      = State.Eval s [CekValue.VCon (.Integer 3)] M := by
  obtain ⟨k, -, hk⟩ := addTerm_returns (Frame.RightApplicationOfValue (CekValue.VLam M []) :: s)
  refine ⟨3 + k + 1, ?_⟩
  rw [stepN_add, stepN_add]
  show stepN _ (stepN _ (State.Eval (Frame.RightApplicationOfValue (CekValue.VLam M []) :: s)
    [] addTerm) k) 1 = _
  rw [hk]
  rfl

/--
info: 'PlutusCore.UPLC.CekMachine.step_appendStack' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms step_appendStack

/--
info: 'PlutusCore.UPLC.CekMachine.runStepsCosting_appendStack' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runStepsCosting_appendStack

/--
info: 'PlutusCore.UPLC.CekMachine.stepN_appendStack' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stepN_appendStack

/--
info: 'PlutusCore.UPLC.CekMachine.stepN_stack_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stepN_stack_independent

/--
info: 'PlutusCore.UPLC.CekMachine.runStepsWithCost_stack_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms runStepsWithCost_stack_independent

/--
info: 'PlutusCore.UPLC.CekMachine.runSteps_stack_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runSteps_stack_independent

/--
info: 'PlutusCore.UPLC.CekMachine.runStepsWithCost_halt_stack_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms runStepsWithCost_halt_stack_independent

/--
info: 'PlutusCore.UPLC.CekMachine.addProgram_halts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms addProgram_halts

/--
info: 'PlutusCore.UPLC.CekMachine.addTerm_returns' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms addTerm_returns

/--
info: 'PlutusCore.UPLC.CekMachine.applyIdentity_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms applyIdentity_cost

end PlutusCore.UPLC.CekMachine
