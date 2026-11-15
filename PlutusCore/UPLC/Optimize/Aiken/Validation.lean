import PlutusCore.UPLC.Optimize.Aiken.ValidationCode
import PlutusCore.UPLC.Optimize.RunSteps

namespace PlutusCore.UPLC.Optimize.Aiken
open PlutusCore.Default
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

/-- A compact, total account of the compiled traversal. Invalid prefixes do
    not pay for pending list reconstruction; successful traversals do. -/
def validationPlan : List Data → ValidationPlan
  | [] => .valid 16
  | .B b :: xs =>
    if validKey b then
      match validationPlan xs with
      | .valid c => .valid (c + 81)
      | .invalid c => .invalid (c + 80)
    else .invalid 56
  | _ :: _ => .invalid 27

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

theorem validation_plan_correct (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) :
    PlanCorrect sem (validationEntry k caps xs) k xs (validationPlan xs) := by
  induction xs generalizing k with
  | nil => exact validation_nil_block a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k
  | cons d xs ih =>
    cases d with
    | B b =>
      by_cases hb : validKey b = true
      · have block := validation_cons_block a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k b xs hb
        have tailCorrect := ih (prependFrame b :: k)
        cases hp : validationPlan xs with
        | valid cost =>
          simp only [hp, PlanCorrect] at tailCorrect
          simp only [validationPlan, hb, ↓reduceIte, hp, PlanCorrect]
          have hc : cost + 81 = (80 + cost) + 1 := by omega
          rw [hc, preserving_add, preserving_add, block, tailCorrect]
          exact prepend_block sem k b xs
        | invalid cost =>
          simp only [hp, PlanCorrect] at tailCorrect
          have hpos : 0 < cost := by
            cases cost with
            | zero => simp [validationEntry] at tailCorrect
            | succ c => omega
          simp only [validationPlan, hb, ↓reduceIte, hp, PlanCorrect]
          constructor
          · have hc : cost + 80 - 1 = 80 + (cost - 1) := by omega
            rw [hc, preserving_add, block]
            exact tailCorrect.1
          · rw [Nat.add_comm cost 80, preserving_add, block]
            exact tailCorrect.2
      · have hf : validKey b = false := by cases h : validKey b <;> simp_all
        simp only [validationPlan, hf, Bool.false_eq_true, ↓reduceIte, PlanCorrect]
        exact ⟨validation_badlength_live a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k b xs hf,
          validation_badlength_error a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k b xs hf⟩
    | Constr i fields =>
      exact ⟨validation_nonbyte_live a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k (.Constr i fields) xs,
        validation_nonbyte_error a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k (.Constr i fields) xs rfl⟩
    | Map entries =>
      exact ⟨validation_nonbyte_live a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k (.Map entries) xs,
        validation_nonbyte_error a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k (.Map entries) xs rfl⟩
    | List entries =>
      exact ⟨validation_nonbyte_live a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k (.List entries) xs,
        validation_nonbyte_error a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k (.List entries) xs rfl⟩
    | I i =>
      exact ⟨validation_nonbyte_live a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k (.I i) xs,
        validation_nonbyte_error a0 a1 a2 a3 a4 a5 a6 a7 p q tail sem k (.I i) xs rfl⟩

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
