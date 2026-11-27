import PlutusCore.UPLC.Optimize.ListTraversal

namespace PlutusCore.UPLC.Optimize.ScalarSearch
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

inductive Comparison where
  | eq | lt | le
deriving Repr, BEq

def Comparison.integerBuiltin : Comparison → BuiltinFun
  | .eq => .EqualsInteger
  | .lt => .LessThanInteger
  | .le => .LessThanEqualsInteger

def Comparison.bytesBuiltin : Comparison → BuiltinFun
  | .eq => .EqualsByteString
  | .lt => .LessThanByteString
  | .le => .LessThanEqualsByteString

/-- The reusable scalar-search family has no beneficiary, key length,
    transaction field, script purpose, or fixed needle. -/
inductive Predicate where
  | integer (comparison : Comparison) (needle : Int)
  | bytes (comparison : Comparison) (needle : ByteString)
deriving Repr

def Predicate.decoder : Predicate → BuiltinFun
  | .integer .. => .UnIData
  | .bytes .. => .UnBData

def Predicate.comparator : Predicate → BuiltinFun
  | .integer c _ => c.integerBuiltin
  | .bytes c _ => c.bytesBuiltin

def Predicate.needle : Predicate → Const
  | .integer _ n => .Integer n
  | .bytes _ b => .ByteString b

/-- Capture positions are parameters, not compiler- or validator-fixed offsets. -/
structure Layout where
  ifIndex : Nat
  chooseIndex : Nat
  headIndex : Nat
  tailIndex : Nat
 deriving Repr

structure Bindings where
  env : Environment
  layout : Layout
  ifBound : env[layout.ifIndex]? =
    some (.VBuiltin .IfThenElse [] (ArgV ⊙ ArgV ⊙ a[ArgV]))
  chooseBound : env[layout.chooseIndex]? =
    some (.VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]))
  headBound : env[layout.headIndex]? = some (.VBuiltin .HeadList [] a[ArgV])
  tailBound : env[layout.tailIndex]? = some (.VBuiltin .TailList [] a[ArgV])

def Predicate.test (p : Predicate) (headIndex : Nat) : Term :=
  .Apply (.Apply (.Builtin p.comparator)
    (.Apply (.Builtin p.decoder) (.Apply (.Var (headIndex + 2)) (.Var 0)))) (.Const p.needle)

def Predicate.check (p : Predicate) (sem : BuiltinSemanticsVariant) (d : Data) : Option Bool := do
  let v ← evaluateBuiltinFunction sem p.decoder [.VCon (.Data d)]
  match ← evaluateBuiltinFunction sem p.comparator [.VCon p.needle, v] with
  | .VCon (.Bool b) => some b
  | _ => none

/-- Common self-application / chooseList / conditional recursion skeleton.
    The scalar operation is a parameter, rather than a literal compiler body. -/
def body (layout : Layout) (test : Term) : Term :=
  .Force (.Case (.Constr 0 [
    .Var 0, .Delay (.Const (.Bool false)),
    .Delay (.Force (.Case (.Constr 0 [test,
      .Delay (.Const (.Bool true)),
      .Delay (.Apply (.Apply (.Var 1) (.Var 1))
        (.Apply (.Var (layout.tailIndex + 2)) (.Var 0)))])
      [.Var (layout.ifIndex + 2)]))]) [.Var (layout.chooseIndex + 2)])

def entry (p : Predicate) (bindings : Bindings) (k : Stack) (xs : List Data) : State :=
  let code := body bindings.layout (p.test bindings.layout.headIndex)
  .Eval k (.VCon (.ConstDataList xs) :: .VLam (.Lam code) bindings.env :: bindings.env) code

/-- Local reduction set for bounded CEK certificates; no recursive loop is unfolded. -/
local macro "scalar_simp" : tactic =>
  `(tactic| simp_all [entry, body, Predicate.test, Predicate.decoder, Predicate.comparator,
      Predicate.needle, Predicate.check, Comparison.integerBuiltin, Comparison.bytesBuiltin,
      runStepsPreservingState, step, step.folding, evalBuiltin, expectedArgs, List.get?Internal,
      evaluateBuiltinFunction,
      PlutusCore.UPLC.BuiltinFunctions.List.chooseList,
      PlutusCore.UPLC.BuiltinFunctions.List.headList,
      PlutusCore.UPLC.BuiltinFunctions.List.tailList,
      PlutusCore.UPLC.BuiltinFunctions.Data.unBData,
      PlutusCore.UPLC.BuiltinFunctions.Data.unIData,
      PlutusCore.UPLC.BuiltinFunctions.Integer.equalsInteger,
      PlutusCore.UPLC.BuiltinFunctions.Integer.lessThanInteger,
      PlutusCore.UPLC.BuiltinFunctions.Integer.lessThanEqualsInteger,
      PlutusCore.UPLC.BuiltinFunctions.ByteString.equalsByteString,
      PlutusCore.UPLC.BuiltinFunctions.ByteString.lessThanByteString,
      PlutusCore.UPLC.BuiltinFunctions.ByteString.lessThanEqualsByteString,
      PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
      PlutusCore.List.headList, PlutusCore.List.tailList,
      PlutusCore.Data.unBData, PlutusCore.Data.unIData,
      PlutusCore.Bool.ifThenElse, Live])

section Blocks
variable (bindings : Bindings)

theorem empty_block (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack) :
    runStepsPreservingState sem (entry p bindings k []) 16 = .Return k (.VCon (.Bool false)) := by
  cases bindings
  scalar_simp

theorem found_block (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (d : Data) (xs : List Data) (h : p.check sem d = some true) :
    runStepsPreservingState sem (entry p bindings k (d :: xs)) 47 = .Return k (.VCon (.Bool true)) := by
  cases bindings
  cases p with
  | integer c n => cases c <;> cases d <;> scalar_simp
  | bytes c b => cases c <;> cases d <;> scalar_simp

theorem next_block (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (d : Data) (xs : List Data) (h : p.check sem d = some false) :
    runStepsPreservingState sem (entry p bindings k (d :: xs)) 60 = entry p bindings k xs := by
  cases bindings
  cases p with
  | integer c n => cases c <;> cases d <;> scalar_simp
  | bytes c b => cases c <;> cases d <;> scalar_simp

theorem reject_block (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (d : Data) (xs : List Data) (h : p.check sem d = none) :
    runStepsPreservingState sem (entry p bindings k (d :: xs)) 31 = .Error := by
  cases bindings
  cases p with
  | integer c n => cases c <;> cases d <;> scalar_simp
  | bytes c b => cases c <;> cases d <;> scalar_simp

theorem reject_live (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (d : Data) (xs : List Data) :
    Live (runStepsPreservingState sem (entry p bindings k (d :: xs)) 30) := by
  cases bindings
  cases p with
  | integer c n => cases c <;> scalar_simp
  | bytes c b => cases c <;> scalar_simp

def inspect (p : Predicate) (sem : BuiltinSemanticsVariant) (d : Data) : SearchStep :=
  match p.check sem d with
  | some true => .found 47
  | some false => .next 60
  | none => .reject 30

/-- All six scalar predicates use the same search induction theorem. -/
def certificate (p : Predicate) (sem : BuiltinSemanticsVariant) : Search sem Data where
  entry := entry p bindings
  render := fun found => .VCon (.Bool found.isSome)
  nilCost := 16
  inspect := inspect p sem
  empty := empty_block bindings p sem
  found := by
    intro k d xs n h
    cases hc : p.check sem d with
    | none => simp [inspect, hc] at h
    | some b =>
      cases b with
      | false => simp [inspect, hc] at h
      | true =>
        simp [inspect, hc] at h; subst n
        exact found_block bindings p sem k d xs hc
  next := by
    intro k d xs n h
    cases hc : p.check sem d with
    | none => simp [inspect, hc] at h
    | some b =>
      cases b with
      | true => simp [inspect, hc] at h
      | false =>
        simp [inspect, hc] at h; subst n
        exact next_block bindings p sem k d xs hc
  reject := by
    intro k d xs n h
    cases hc : p.check sem d with
    | some b => cases b <;> simp [inspect, hc] at h
    | none =>
      simp [inspect, hc] at h; subst n
      exact ⟨reject_live bindings p sem k d xs,
        reject_block bindings p sem k d xs hc⟩

def summary (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) : State :=
  Plan.execute sem k (searchPlan (fun found => .VCon (.Bool found.isSome))
    16 (inspect p sem) xs) fuel

theorem run_summary (p : Predicate) (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) :
    runSteps sem (entry p bindings k xs) fuel =
      summary p sem k xs fuel :=
  (certificate bindings p sem).run_eq k xs fuel

end Blocks
end PlutusCore.UPLC.Optimize.ScalarSearch
