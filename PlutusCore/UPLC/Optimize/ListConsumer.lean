import PlutusCore.UPLC.Optimize.ListLength
import PlutusCore.UPLC.Optimize.Composition

namespace PlutusCore.UPLC.Optimize.ListConsumer
open PlutusCore.Default PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Builtins PlutusCore.UPLC.Term
open PlutusCore.UPLC.Builtins.ExpectedBuiltinArg
open PlutusCore.UPLC.Builtins.ExpectedArgNotations

def branchPlan (before : Nat) (accept : Bool) : Plan CekValue :=
  if accept then .done before (.VCon .Unit) else .error before

def guardStack (env : PlutusCore.UPLC.CekValue.Environment) (errorArgument : Term) : Stack :=
  let rho := .VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]) :: env
  [.ConstructorArgument 0 [] [.Delay (.Const .Unit), .Delay (.Apply .Error errorArgument)] rho,
    .CaseScrutinee [.Var 0] rho, .ForceFrame]

def leStack (argEnv env : PlutusCore.UPLC.CekValue.Environment)
    (errorArgument : Term) (bound : Int) : Stack :=
  .RightApplicationOfValue (.VBuiltin .LessThanEqualsInteger [] (ArgV ⊙ a[ArgV])) ::
    .LeftApplicationToTerm (.Const (.Integer bound)) argEnv :: guardStack env errorArgument

def positiveStack (env : PlutusCore.UPLC.CekValue.Environment) (errorArgument : Term) : Stack :=
  .RightApplicationOfValue (.VBuiltin .LessThanInteger [.VCon (.Integer 0)] a[ArgV]) ::
    guardStack env errorArgument

set_option maxRecDepth 20000
local macro "consumer_reduce" : tactic =>
  `(tactic| simp_all [Plan.Correct, branchPlan, leStack, positiveStack, guardStack,
    Live, runStepsPreservingState, step, step.folding, evalBuiltin, expectedArgs,
    List.get?Internal, PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
    PlutusCore.UPLC.BuiltinFunctions.Integer.lessThanInteger,
    PlutusCore.UPLC.BuiltinFunctions.Integer.lessThanEqualsInteger,
    PlutusCore.Bool.ifThenElse])

theorem consume_le (sem : BuiltinSemanticsVariant)
    (argEnv env : PlutusCore.UPLC.CekValue.Environment) (errorArgument : Term) (bound n : Int) :
    Plan.Correct sem (.Return (leStack argEnv env errorArgument bound) (.VCon (.Integer n))) []
      (branchPlan 16 (PlutusCore.Integer.lessThanEqualsInteger n bound)) := by
  cases h : PlutusCore.Integer.lessThanEqualsInteger n bound <;> consumer_reduce

theorem consume_positive (sem : BuiltinSemanticsVariant)
    (env : PlutusCore.UPLC.CekValue.Environment) (errorArgument : Term) (n : Int) :
    Plan.Correct sem (.Return (positiveStack env errorArgument) (.VCon (.Integer n))) []
      (branchPlan 13 (PlutusCore.Integer.lessThanInteger 0 n)) := by
  cases h : PlutusCore.Integer.lessThanInteger 0 n <;> consumer_reduce

/-- A complete program supplies two finite blocks around the shared unbounded
    length traversal. Parameters may include an entire symbolic ScriptContext. -/
structure Certificate (sem : BuiltinSemanticsVariant) (γ : Type) where
  entry : γ → State
  elements : γ → List Data
  bindings : γ → ListLength.Bindings
  stack : γ → Stack
  prefixCost : Nat
  postCost : Nat
  test : Int → Bool
  prefixProof : ∀ p, runStepsPreservingState sem (entry p) prefixCost =
    ListLength.entry (bindings p) (stack p) (elements p)
  consume : ∀ p n, Plan.Correct sem (.Return (stack p) (.VCon (.Integer n))) []
    (branchPlan postCost (test n))

namespace Certificate

def cost (spec : Certificate sem γ) (p : γ) : Nat :=
  spec.prefixCost + 37 * (spec.elements p).length + 16 + spec.postCost

/-- Exact semantics for all fuel, not merely a proof with a large fixed
    budget. List elements and all unrelated parameters remain arbitrary. -/
theorem run_eq (spec : Certificate sem γ) (p : γ) (fuel : Nat) :
    runSteps sem (spec.entry p) fuel =
      if fuel ≤ spec.cost p then .BudgetExhausted
      else if spec.test (spec.elements p).length then .Halt (.VCon .Unit) else .Error := by
  let n := 37 * (spec.elements p).length + 16
  have loop := (ListLength.certificate (spec.bindings p) sem).correct
    (spec.stack p) (spec.elements p)
  have hl : runStepsPreservingState sem
      (ListLength.entry (spec.bindings p) (spec.stack p) (spec.elements p)) n =
        .Return (spec.stack p) (.VCon (.Integer (spec.elements p).length)) := by
    simpa only [Traversal.plan, ListLength.certificate, ListLength.plan_eq,
      Plan.Correct, ListLength.render, n] using loop
  have block : runStepsPreservingState sem (spec.entry p) (spec.prefixCost + n) =
      .Return (spec.stack p) (.VCon (.Integer (spec.elements p).length)) := by
    rw [preserving_add, spec.prefixProof p, hl]
  have full := Plan.correct_shift sem (spec.entry p) _ [] (spec.prefixCost + n)
    _ block (spec.consume p (spec.elements p).length)
  rw [Plan.run_eq sem _ [] _ full fuel, Composition.execute_empty]
  cases h : spec.test (spec.elements p).length <;>
    simp [branchPlan, Plan.shift, Composition.finish, cost, n, Nat.add_assoc]

theorem accepts_iff (spec : Certificate sem γ) (p : γ) (fuel : Nat) :
    runSteps sem (spec.entry p) fuel = .Halt (.VCon .Unit) ↔
      spec.test (spec.elements p).length = true ∧ spec.cost p < fuel := by
  rw [spec.run_eq]
  by_cases hf : fuel ≤ spec.cost p <;>
    cases ht : spec.test (spec.elements p).length <;> simp [hf] <;> omega

theorem eventually_accepts_iff (spec : Certificate sem γ) (p : γ) :
    (∃ fuel, runSteps sem (spec.entry p) fuel = .Halt (.VCon .Unit)) ↔
      spec.test (spec.elements p).length = true := by
  constructor
  · rintro ⟨fuel, h⟩; exact ((spec.accepts_iff p fuel).mp h).1
  · intro h
    exact ⟨spec.cost p + 1, (spec.accepts_iff p _).mpr ⟨h, by omega⟩⟩

end Certificate
end PlutusCore.UPLC.Optimize.ListConsumer
