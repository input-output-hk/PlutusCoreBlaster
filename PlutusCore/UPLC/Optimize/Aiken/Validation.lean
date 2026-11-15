import PlutusCore.UPLC.Optimize.Aiken.ValidationCode
import PlutusCore.UPLC.Optimize.ListTraversal

namespace PlutusCore.UPLC.Optimize.Aiken
open PlutusCore.Default
open PlutusCore.UPLC.Optimize
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.Builtins.ExpectedBuiltinArg
open PlutusCore.UPLC.Builtins.ExpectedArgNotations
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- Captures not inspected by this loop are arbitrary. The trailing environment
    is also arbitrary; it may contain the whole enclosing script context. -/
def validationCaptures
    (a0 a1 a2 a3 a4 a5 a6 a7 p q : CekValue) (tail : Environment) : Environment :=
  a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 ::
  .VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]) :: p :: q ::
  .VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]) ::
  .VBuiltin .MkCons [] (ArgV ⊙ a[ArgV]) ::
  .VBuiltin .HeadList [] a[ArgV] :: .VBuiltin .TailList [] a[ArgV] :: tail

def validationEntry (k : Stack) (captures : Environment) (xs : List Data) : State :=
  .Eval k (.VCon (.ConstDataList xs) :: .VLam (.Lam validationBody) captures :: captures) validationBody

def prependFrame (b : ByteString) : Frame :=
  .RightApplicationOfValue (.VBuiltin .MkCons [.VCon (.Data (.B b))] a[ArgV])

def validKey (b : ByteString) : Bool :=
  (28 : Int) == PlutusCore.ByteString.lengthOfByteString b

inductive ValidationPlan where
  | valid (cost : Nat)
  | invalid (cost : Nat)
deriving Repr, BEq

/-- This adapter describes the old fixture's element check; the list induction
    itself lives in the validator-independent `Traversal` theorem. -/
def validationInspect : Data → TraversalStep
  | .B b => if validKey b then .descend 80 1 else .reject 55
  | _ => .reject 26

def validationGenericPlan (xs : List Data) : Plan CekValue :=
  traversalPlan (fun xs => .VCon (.ConstDataList xs)) 16 validationInspect xs

/-- Retain the original experiment's public result type. -/
def validationPlan (xs : List Data) : ValidationPlan :=
  match validationGenericPlan xs with
  | .done cost _ => .valid cost
  | .error before => .invalid (before + 1)

def validationSummary (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) : State :=
  match validationPlan xs with
  | .valid cost =>
    if fuel < cost then .BudgetExhausted
    else runSteps sem (.Return k (.VCon (.ConstDataList xs))) (fuel - cost)
  | .invalid cost => if fuel < cost then .BudgetExhausted else .Error

def PlanCorrect (sem : BuiltinSemanticsVariant) (s : State) (k : Stack)
    (xs : List Data) : ValidationPlan → Prop
  | .valid cost =>
    runStepsPreservingState sem s cost = .Return k (.VCon (.ConstDataList xs))
  | .invalid cost =>
    Live (runStepsPreservingState sem s (cost - 1)) ∧
    runStepsPreservingState sem s cost = .Error

section Blocks
variable (a0 a1 a2 a3 a4 a5 a6 a7 p q : CekValue) (tail : Environment)
local notation "caps" => validationCaptures a0 a1 a2 a3 a4 a5 a6 a7 p q tail

theorem validation_nil_block (sem : BuiltinSemanticsVariant) (k : Stack) :
    runStepsPreservingState sem (validationEntry k caps []) 16 =
      .Return k (.VCon (.ConstDataList [])) := by
  rfl

theorem prepend_block (sem : BuiltinSemanticsVariant) (k : Stack)
    (b : ByteString) (xs : List Data) :
    step sem (.Return (prependFrame b :: k) (.VCon (.ConstDataList xs))) =
      .Return k (.VCon (.ConstDataList (.B b :: xs))) := by
  rfl

theorem validation_cons_block (sem : BuiltinSemanticsVariant) (k : Stack)
    (b : ByteString) (xs : List Data) (h : validKey b = true) :
    runStepsPreservingState sem (validationEntry k caps (.B b :: xs)) 80 =
      validationEntry (prependFrame b :: k) caps xs := by
  simp only [validKey] at h
  simp [Live, validationEntry, validationCaptures, validationBody, prependFrame,
    runStepsPreservingState, step, step.folding, evalBuiltin, expectedArgs, List.get?Internal,
    PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    PlutusCore.UPLC.BuiltinFunctions.List.chooseList,
    PlutusCore.UPLC.BuiltinFunctions.List.headList,
    PlutusCore.UPLC.BuiltinFunctions.List.tailList,
    PlutusCore.UPLC.BuiltinFunctions.List.mkCons,
    PlutusCore.UPLC.BuiltinFunctions.Data.unBData,
    PlutusCore.UPLC.BuiltinFunctions.Data.bData,
    PlutusCore.UPLC.BuiltinFunctions.ByteString.lengthOfByteString,
    PlutusCore.UPLC.BuiltinFunctions.Integer.equalsInteger,
    PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
    PlutusCore.Integer.equalsInteger, PlutusCore.Bool.ifThenElse,
    PlutusCore.List.tailList, PlutusCore.List.mkCons, PlutusCore.Data.bData, h]

def nonByte (d : Data) : Bool := match d with | .B _ => false | _ => true

theorem validation_nonbyte_live (sem : BuiltinSemanticsVariant) (k : Stack)
    (d : Data) (xs : List Data) :
    Live (runStepsPreservingState sem (validationEntry k caps (d :: xs)) 26) := by
  trivial

theorem validation_nonbyte_error (sem : BuiltinSemanticsVariant) (k : Stack)
    (d : Data) (xs : List Data) (h : nonByte d = true) :
    runStepsPreservingState sem (validationEntry k caps (d :: xs)) 27 = .Error := by
  cases d <;> first | rfl | simp [nonByte] at h

theorem validation_badlength_live (sem : BuiltinSemanticsVariant) (k : Stack)
    (b : ByteString) (xs : List Data) (h : validKey b = false) :
    Live (runStepsPreservingState sem (validationEntry k caps (.B b :: xs)) 55) := by
  simp only [validKey] at h
  simp [Live, validationEntry, validationCaptures, validationBody, prependFrame,
    runStepsPreservingState, step, step.folding, evalBuiltin, expectedArgs, List.get?Internal,
    PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    PlutusCore.UPLC.BuiltinFunctions.List.chooseList,
    PlutusCore.UPLC.BuiltinFunctions.List.headList,
    PlutusCore.UPLC.BuiltinFunctions.List.tailList,
    PlutusCore.UPLC.BuiltinFunctions.List.mkCons,
    PlutusCore.UPLC.BuiltinFunctions.Data.unBData,
    PlutusCore.UPLC.BuiltinFunctions.Data.bData,
    PlutusCore.UPLC.BuiltinFunctions.ByteString.lengthOfByteString,
    PlutusCore.UPLC.BuiltinFunctions.Integer.equalsInteger,
    PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
    PlutusCore.Integer.equalsInteger, PlutusCore.Bool.ifThenElse,
    PlutusCore.List.tailList, PlutusCore.List.mkCons, PlutusCore.Data.bData, h]

theorem validation_badlength_error (sem : BuiltinSemanticsVariant) (k : Stack)
    (b : ByteString) (xs : List Data) (h : validKey b = false) :
    runStepsPreservingState sem (validationEntry k caps (.B b :: xs)) 56 = .Error := by
  simp only [validKey] at h
  simp [Live, validationEntry, validationCaptures, validationBody, prependFrame,
    runStepsPreservingState, step, step.folding, evalBuiltin, expectedArgs, List.get?Internal,
    PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    PlutusCore.UPLC.BuiltinFunctions.List.chooseList,
    PlutusCore.UPLC.BuiltinFunctions.List.headList,
    PlutusCore.UPLC.BuiltinFunctions.List.tailList,
    PlutusCore.UPLC.BuiltinFunctions.List.mkCons,
    PlutusCore.UPLC.BuiltinFunctions.Data.unBData,
    PlutusCore.UPLC.BuiltinFunctions.Data.bData,
    PlutusCore.UPLC.BuiltinFunctions.ByteString.lengthOfByteString,
    PlutusCore.UPLC.BuiltinFunctions.Integer.equalsInteger,
    PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
    PlutusCore.Integer.equalsInteger, PlutusCore.Bool.ifThenElse,
    PlutusCore.List.tailList, PlutusCore.List.mkCons, PlutusCore.Data.bData, h]

/-- Only bounded compiler blocks are specific to this fixture. -/
def validationTraversal (sem : BuiltinSemanticsVariant) : Traversal sem Data where
  entry := fun k xs => validationEntry k caps xs
  render := fun xs => .VCon (.ConstDataList xs)
  frame := fun d => match d with | .B b => prependFrame b | _ => .ForceFrame
  nilCost := 16
  inspect := validationInspect
  empty := validation_nil_block a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem
  descend := by
    intro k d xs before after h
    cases d with
    | B b =>
      by_cases hb : validKey b = true
      · simp [validationInspect, hb] at h
        obtain ⟨rfl, rfl⟩ := h
        exact validation_cons_block a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k b xs hb
      · simp [validationInspect, hb] at h
    | _ => simp [validationInspect] at h
  unwind := by
    intro k d xs before after h
    cases d with
    | B b =>
      by_cases hb : validKey b = true
      · simp [validationInspect, hb] at h
        obtain ⟨rfl, rfl⟩ := h
        exact prepend_block sem k b xs
      · simp [validationInspect, hb] at h
    | _ => simp [validationInspect] at h
  reject := by
    intro k d xs n h
    cases d with
    | B b =>
      by_cases hb : validKey b = true
      · simp [validationInspect, hb] at h
      · have hf : validKey b = false := by cases hv : validKey b <;> simp_all
        simp [validationInspect, hf] at h; subst n
        exact ⟨validation_badlength_live a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k b xs hf,
          validation_badlength_error a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k b xs hf⟩
    | _ =>
      simp [validationInspect] at h; subst n
      exact ⟨validation_nonbyte_live a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k _ xs,
        validation_nonbyte_error a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k _ xs rfl⟩

theorem validation_plan_correct (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) :
    PlanCorrect sem (validationEntry k caps xs) k xs (validationPlan xs) := by
  have correct := (validationTraversal a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem).correct k xs
  change Plan.Correct sem (validationEntry k caps xs) k (validationGenericPlan xs) at correct
  cases hp : validationGenericPlan xs with
  | done cost value =>
    have hv := traversalPlan_done_value (fun xs => .VCon (.ConstDataList xs))
      16 validationInspect xs cost value hp
    simpa [validationPlan, hp, PlanCorrect, Plan.Correct, hv] using correct
  | error before =>
    simpa [validationPlan, hp, PlanCorrect, Plan.Correct] using correct

/-- Exact finite-fuel equivalence for arbitrary encoded lists, including every
    malformed-data, invalid-length and insufficient-fuel case. -/
theorem validation_run_summary (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) :
    runSteps sem (validationEntry k caps xs) fuel = validationSummary sem k xs fuel := by
  have correct := validation_plan_correct a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k xs
  cases hp : validationPlan xs with
  | valid cost =>
    simp only [hp, PlanCorrect] at correct
    have live : Live (runStepsPreservingState sem (validationEntry k caps xs) cost) := by
      rw [correct]; trivial
    simpa [validationSummary, hp, correct] using
      runSteps_of_live_prefix sem (validationEntry k caps xs) cost live fuel
  | invalid cost =>
    simp only [hp, PlanCorrect] at correct
    have hpos : 0 < cost := by
      cases cost with
      | zero => simp [validationEntry] at correct
      | succ c => omega
    have he : runStepsPreservingState sem (validationEntry k caps xs) (cost - 1 + 1) = .Error := by
      simpa [show cost - 1 + 1 = cost by omega] using correct.2
    have bound : fuel ≤ cost - 1 ↔ fuel < cost := by omega
    simpa [validationSummary, hp, bound] using
      runSteps_of_error_prefix sem (validationEntry k caps xs) (cost - 1) correct.1 he fuel


end Blocks
end PlutusCore.UPLC.Optimize.Aiken
