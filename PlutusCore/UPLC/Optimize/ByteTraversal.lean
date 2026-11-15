import PlutusCore.UPLC.Optimize.ScalarSearch

namespace PlutusCore.UPLC.Optimize.ByteTraversal
open PlutusCore.Default
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.Builtins.ExpectedBuiltinArg
open PlutusCore.UPLC.Builtins.ExpectedArgNotations
open PlutusCore.UPLC.BuiltinFunctions.Evaluate
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- The literal bound and the relation are parameters. The relation compares
    the bound with the byte length, matching the compiled operand order. -/
structure Predicate where
  comparison : ScalarSearch.Comparison
  bound : Int
deriving Repr

def Predicate.test (p : Predicate) : Term :=
  .Apply (.Apply (.Builtin p.comparison.integerBuiltin) (.Const (.Integer p.bound)))
    (.Apply (.Builtin .LengthOfByteString) (.Var 0))

def Predicate.check (p : Predicate) (sem : BuiltinSemanticsVariant) (b : ByteString) : Bool :=
  match evaluateBuiltinFunction sem p.comparison.integerBuiltin
      [.VCon (.Integer (PlutusCore.ByteString.lengthOfByteString b)), .VCon (.Integer p.bound)] with
  | some (.VCon (.Bool result)) => result
  | _ => false

structure Bindings where
  base : ScalarSearch.Bindings
  consIndex : Nat
  consBound : base.env[consIndex]? = some (.VBuiltin .MkCons [] (ArgV ⊙ a[ArgV]))

def body (layout : ScalarSearch.Layout) (consIndex : Nat) (test : Term) : Term :=
  .Force (.Case (.Constr 0 [
    .Var 0, .Delay (.Const (.ConstDataList [])),
    .Delay (.Apply (.Lam (.Force (.Case (.Constr 0 [test,
      .Delay (.Apply (.Apply (.Var (consIndex + 3)) (.Apply (.Builtin .BData) (.Var 0)))
        (.Apply (.Apply (.Var 2) (.Var 2)) (.Apply (.Var (layout.tailIndex + 3)) (.Var 1)))),
      .Delay .Error]) [.Var (layout.ifIndex + 3)])))
      (.Apply (.Builtin .UnBData) (.Apply (.Var (layout.headIndex + 2)) (.Var 0))))])
    [.Var (layout.chooseIndex + 2)])

def entry (p : Predicate) (bindings : Bindings) (k : Stack) (xs : List Data) : State :=
  let code := body bindings.base.layout bindings.consIndex p.test
  .Eval k (.VCon (.ConstDataList xs) :: .VLam (.Lam code) bindings.base.env :: bindings.base.env) code

def prepend (b : ByteString) : Frame :=
  .RightApplicationOfValue (.VBuiltin .MkCons [.VCon (.Data (.B b))] a[ArgV])

def inspect (p : Predicate) (sem : BuiltinSemanticsVariant) : Data → TraversalStep
  | .B b => if p.check sem b then .descend 80 1 else .reject 55
  | _ => .reject 26

local macro "byte_simp" : tactic =>
  `(tactic| simp_all [entry, body, Predicate.test, Predicate.check,
    ScalarSearch.Comparison.integerBuiltin, prepend, Live,
    runStepsPreservingState, step, step.folding, evalBuiltin, expectedArgs, List.get?Internal,
    evaluateBuiltinFunction,
    PlutusCore.UPLC.BuiltinFunctions.List.chooseList,
    PlutusCore.UPLC.BuiltinFunctions.List.headList,
    PlutusCore.UPLC.BuiltinFunctions.List.tailList,
    PlutusCore.UPLC.BuiltinFunctions.List.mkCons,
    PlutusCore.UPLC.BuiltinFunctions.Data.unBData,
    PlutusCore.UPLC.BuiltinFunctions.Data.bData,
    PlutusCore.UPLC.BuiltinFunctions.ByteString.lengthOfByteString,
    PlutusCore.UPLC.BuiltinFunctions.Integer.equalsInteger,
    PlutusCore.UPLC.BuiltinFunctions.Integer.lessThanInteger,
    PlutusCore.UPLC.BuiltinFunctions.Integer.lessThanEqualsInteger,
    PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
    PlutusCore.Bool.ifThenElse, PlutusCore.List.tailList, PlutusCore.List.mkCons,
    PlutusCore.Data.unBData, PlutusCore.Data.bData])

section Blocks
variable (bindings : Bindings)

theorem empty_block (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack) :
    runStepsPreservingState sem (entry p bindings k []) 16 = .Return k (.VCon (.ConstDataList [])) := by
  rcases bindings with ⟨⟨env, layout, hi, hc, hh, ht⟩, ci, hm⟩
  byte_simp

theorem descend_block (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (b : ByteString) (xs : List Data) (h : p.check sem b = true) :
    runStepsPreservingState sem (entry p bindings k (.B b :: xs)) 80 =
      entry p bindings (prepend b :: k) xs := by
  rcases bindings with ⟨⟨env, layout, hi, hc, hh, ht⟩, ci, hm⟩
  rcases p with ⟨comparison, bound⟩
  cases comparison <;> byte_simp

theorem unwind_block (sem : BuiltinSemanticsVariant) (k : Stack)
    (b : ByteString) (xs : List Data) :
    runStepsPreservingState sem (.Return (prepend b :: k) (.VCon (.ConstDataList xs))) 1 =
      .Return k (.VCon (.ConstDataList (.B b :: xs))) := by rfl

theorem bad_length_live (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (b : ByteString) (xs : List Data) (h : p.check sem b = false) :
    Live (runStepsPreservingState sem (entry p bindings k (.B b :: xs)) 55) := by
  rcases bindings with ⟨⟨env, layout, hi, hc, hh, ht⟩, ci, hm⟩
  rcases p with ⟨comparison, bound⟩
  cases comparison <;> byte_simp

theorem bad_length_error (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (b : ByteString) (xs : List Data) (h : p.check sem b = false) :
    runStepsPreservingState sem (entry p bindings k (.B b :: xs)) 56 = .Error := by
  rcases bindings with ⟨⟨env, layout, hi, hc, hh, ht⟩, ci, hm⟩
  rcases p with ⟨comparison, bound⟩
  cases comparison <;> byte_simp

def nonByte : Data → Bool
  | .B _ => false
  | _ => true

theorem malformed_live (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (d : Data) (xs : List Data) :
    Live (runStepsPreservingState sem (entry p bindings k (d :: xs)) 26) := by
  rcases bindings with ⟨⟨env, layout, hi, hc, hh, ht⟩, ci, hm⟩
  byte_simp

theorem malformed_error (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (d : Data) (xs : List Data) (h : nonByte d = true) :
    runStepsPreservingState sem (entry p bindings k (d :: xs)) 27 = .Error := by
  rcases bindings with ⟨⟨env, layout, hi, hc, hh, ht⟩, ci, hm⟩
  cases d <;> try (simp [nonByte] at h) <;> byte_simp

def certificate (p : Predicate) (sem : BuiltinSemanticsVariant) : Traversal sem Data where
  entry := entry p bindings
  render := fun xs => .VCon (.ConstDataList xs)
  frame := fun d => match d with | .B b => prepend b | _ => .ForceFrame
  nilCost := 16
  inspect := inspect p sem
  empty := empty_block bindings p sem
  descend := by
    intro k d xs before after h
    cases d with
    | B b =>
      cases hb : p.check sem b <;> simp [inspect, hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact descend_block bindings p sem k b xs hb
    | _ => simp [inspect] at h
  unwind := by
    intro k d xs before after h
    cases d with
    | B b =>
      cases hb : p.check sem b <;> simp [inspect, hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact unwind_block sem k b xs
    | _ => simp [inspect] at h
  reject := by
    intro k d xs n h
    cases d with
    | B b =>
      cases hb : p.check sem b <;> simp [inspect, hb] at h
      subst n
      exact ⟨bad_length_live bindings p sem k b xs hb, bad_length_error bindings p sem k b xs hb⟩
    | _ =>
      simp [inspect] at h; subst n
      exact ⟨malformed_live bindings p sem k _ xs, malformed_error bindings p sem k _ xs rfl⟩

def summary (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) : State :=
  Plan.execute sem k (traversalPlan (fun xs => .VCon (.ConstDataList xs)) 16 (inspect p sem) xs) fuel

theorem run_summary (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) :
    runSteps sem (entry p bindings k xs) fuel = summary p sem k xs fuel :=
  (certificate bindings p sem).run_eq k xs fuel

end Blocks
end PlutusCore.UPLC.Optimize.ByteTraversal
