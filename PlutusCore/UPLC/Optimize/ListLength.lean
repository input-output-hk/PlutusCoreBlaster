import PlutusCore.UPLC.Optimize.ListTraversal

namespace PlutusCore.UPLC.Optimize.ListLength
open PlutusCore.Default PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.Builtins.ExpectedBuiltinArg
open PlutusCore.UPLC.Builtins.ExpectedArgNotations
open PlutusCore.Data (Data)

structure Bindings where
  env : Environment
  chooseIndex : Nat
  tailIndex : Nat
  chooseBound : env[chooseIndex]? = some (.VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]))
  tailBound : env[tailIndex]? = some (.VBuiltin .TailList [] a[ArgV])

def body (chooseIndex tailIndex : Nat) : Term :=
  .Force (.Case (.Constr 0 [.Var 0, .Delay (.Const (.Integer 0)),
    .Delay (.Apply (.Apply (.Builtin .AddInteger) (.Const (.Integer 1)))
      (.Apply (.Apply (.Var 1) (.Var 1)) (.Apply (.Var (tailIndex + 2)) (.Var 0))))])
    [.Var (chooseIndex + 2)])

def entry (b : Bindings) (k : Stack) (xs : List Data) : State :=
  let code := body b.chooseIndex b.tailIndex
  .Eval k (.VCon (.ConstDataList xs) :: .VLam (.Lam code) b.env :: b.env) code

def render (xs : List Data) : CekValue := .VCon (.Integer xs.length)

def increment : Frame :=
  .RightApplicationOfValue (.VBuiltin .AddInteger [.VCon (.Integer 1)] a[ArgV])

set_option maxRecDepth 20000
set_option maxHeartbeats 0

local macro "length_simp" : tactic =>
  `(tactic| simp_all [entry, body, render, increment, runStepsPreservingState,
    step, step.folding, evalBuiltin, expectedArgs, List.get?Internal,
    PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    PlutusCore.UPLC.BuiltinFunctions.List.chooseList,
    PlutusCore.UPLC.BuiltinFunctions.List.tailList,
    PlutusCore.UPLC.BuiltinFunctions.Integer.addInteger,
    PlutusCore.List.tailList, PlutusCore.Integer.addInteger])

theorem empty_block (b : Bindings) (sem : BuiltinSemanticsVariant) (k : Stack) :
    runStepsPreservingState sem (entry b k []) 16 = .Return k (render []) := by
  cases b
  length_simp

theorem unwind_block (sem : BuiltinSemanticsVariant) (k : Stack) (a : Data) (xs : List Data) :
    runStepsPreservingState sem (.Return (increment :: k) (render xs)) 1 =
      .Return k (render (a :: xs)) := by
  length_simp
  simp [Int.add_comm]

theorem descend_block (b : Bindings) (sem : BuiltinSemanticsVariant) (k : Stack)
    (a : Data) (xs : List Data) :
    runStepsPreservingState sem (entry b k (a :: xs)) 36 =
      entry b (increment :: k) xs := by
  cases b
  length_simp

def certificate (b : Bindings) (sem : BuiltinSemanticsVariant) : Traversal sem Data where
  entry := entry b
  render := render
  frame := fun _ => increment
  nilCost := 16
  inspect := fun _ => .descend 36 1
  empty := empty_block b sem
  descend := by
    intro k a xs before after h
    cases h
    exact descend_block b sem k a xs
  unwind := by
    intro k a xs before after h
    cases h
    exact unwind_block sem k a xs
  reject := by intros; contradiction

theorem plan_eq (xs : List Data) :
    traversalPlan render 16 (fun _ => .descend 36 1) xs =
      .done (37 * xs.length + 16) (render xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [traversalPlan, ih, List.length_cons, Nat.mul_add, Nat.mul_one]
    congr 1
    omega

theorem run_summary (b : Bindings) (sem : BuiltinSemanticsVariant) (k : Stack)
    (xs : List Data) (fuel : Nat) :
    runSteps sem (entry b k xs) fuel =
      Plan.execute sem k (.done (37 * xs.length + 16) (render xs)) fuel := by
  have h := (certificate b sem).run_eq k xs fuel
  simpa only [Traversal.plan, certificate, plan_eq] using h

end PlutusCore.UPLC.Optimize.ListLength
