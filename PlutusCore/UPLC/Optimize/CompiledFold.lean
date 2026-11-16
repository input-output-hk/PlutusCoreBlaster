import PlutusCore.UPLC.Optimize.Fold
import PlutusCore.UPLC.Optimize.Callback

namespace PlutusCore.UPLC.Optimize.CompiledFold
open PlutusCore.Default PlutusCore.UPLC.Term PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.Builtins.ExpectedBuiltinArg
open PlutusCore.UPLC.Builtins.ExpectedArgNotations
open PlutusCore.Data (Data)

inductive Kind where | data | pair
def Kind.Item : Kind → Type
  | .data => Data
  | .pair => Data × Data
def Kind.literal : (kind : Kind) → List kind.Item → Const
  | .data, xs => .ConstDataList xs
  | .pair, xs => .ConstPairDataList xs

structure Bindings where
  env : Environment
  chooseIndex : Nat
  tailIndex : Nat
  chooseBound : env[chooseIndex]? = some (.VBuiltin .ChooseList [] (ArgV ⊙ ArgV ⊙ a[ArgV]))
  tailBound : env[tailIndex]? = some (.VBuiltin .TailList [] a[ArgV])

def body (chooseIndex tailIndex : Nat) (callback : Term) : Term :=
  .Force (.Case (.Constr 0 [.Var 1, .Delay (.Var 0),
    .Delay (.Case (.Constr 0 [.Var 2,
      .Apply (.Var (tailIndex + 3)) (.Var 1), callback]) [.Var 2])])
    [.Var (chooseIndex + 3)])

structure Shape where
  chooseIndex : Nat
  tailIndex : Nat
  callback : Term
deriving Repr

/-- Recognize the recursive spine, leaving the entire callback unconstrained. -/
def recognize : Term → Option Shape
  | code@(.Force (.Case (.Constr 0 [.Var 1, .Delay (.Var 0),
      .Delay (.Case (.Constr 0 [.Var 2, .Apply (.Var tail) (.Var 1), cb]) [.Var 2])])
      [.Var choose])) =>
    if choose ≥ 3 && tail ≥ 3 && code == body (choose - 3) (tail - 3) cb then
      some ⟨choose - 3, tail - 3, cb⟩ else none
  | _ => none

def env (kind : Kind) (b : Bindings) (callback : Term)
    (acc : CekValue) (xs : List kind.Item) : Environment :=
  let code := body b.chooseIndex b.tailIndex callback
  acc :: .VCon (kind.literal xs) :: .VLam (.Lam (.Lam code)) b.env :: b.env

def entry (kind : Kind) (b : Bindings) (callback : Term)
    (k : Stack) (acc : CekValue) (xs : List kind.Item) : State :=
  .Eval k (env kind b callback acc xs) (body b.chooseIndex b.tailIndex callback)

def callbackStack (kind : Kind) (b : Bindings) (callback : Term)
    (acc : CekValue) (a : kind.Item) (xs : List kind.Item) : Stack :=
  let rho := env kind b callback acc (a :: xs)
  [.ConstructorArgument 0 [.VCon (kind.literal xs),
      .VLam (.Lam (.Lam (body b.chooseIndex b.tailIndex callback))) b.env] [] rho,
    .CaseScrutinee [.Var 2] rho]

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

local macro "spine_reduce" : tactic =>
  `(tactic| simp_all [entry, env, body, callbackStack, Kind.literal,
    runStepsPreservingState, step, step.folding, evalBuiltin, expectedArgs,
    List.get?Internal, BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
    BuiltinFunctions.List.chooseList, BuiltinFunctions.List.tailList,
    PlutusCore.List.tailList])

theorem empty_block (kind : Kind) (b : Bindings) (callback : Term)
    (sem : BuiltinSemanticsVariant) (k : Stack) (acc : CekValue) :
    runStepsPreservingState sem (entry kind b callback k acc []) 16 = .Return k acc := by
  cases b
  cases kind <;> spine_reduce

theorem before_block (kind : Kind) (b : Bindings) (callback : Term)
    (sem : BuiltinSemanticsVariant) (k : Stack) (acc : CekValue)
    (a : kind.Item) (xs : List kind.Item) :
    runStepsPreservingState sem (entry kind b callback k acc (a :: xs)) 25 =
      .Eval (callbackStack kind b callback acc a xs ++ k)
        (env kind b callback acc (a :: xs)) callback := by
  cases b
  cases kind <;> spine_reduce

theorem after_block (kind : Kind) (b : Bindings) (callback : Term)
    (sem : BuiltinSemanticsVariant) (k : Stack) (acc result : CekValue)
    (a : kind.Item) (xs : List kind.Item) :
    runStepsPreservingState sem
      (.Return (callbackStack kind b callback acc a xs ++ k) result) 8 =
      entry kind b callback k result xs := by
  cases b
  cases kind <;> spine_reduce

/-- This is the compiler's obligation, checked by the Lean kernel. The
    callback may use arbitrary projections, scalar computations and captures,
    but its returned value/cost must be independent of the tail and caller. -/
structure CompiledCallback (kind : Kind) (b : Bindings) (callback : Term)
    (sem : BuiltinSemanticsVariant) where
  plan : Int → kind.Item → Plan Int
  correct : ∀ acc a xs k,
    Plan.Correct sem (.Eval k (env kind b callback (.VCon (.Integer acc)) (a :: xs)) callback) k
      ((plan acc a).map (fun n => .VCon (.Integer n)))

def inspectPlan {kind : Kind} (plan : Int → kind.Item → Plan Int) (acc : Int) (a : kind.Item) :
    Plan (FoldControl Int CekValue) :=
  match plan acc a with
  | .done n result => .done (25 + n + 8) (.next result)
  | .error n => .error (25 + n)

def inspect (compiled : CompiledCallback kind b callback sem) := inspectPlan compiled.plan

def certificate (compiled : CompiledCallback kind b callback sem) : Fold sem kind.Item Int where
  entry := fun k acc xs => entry kind b callback k (.VCon (.Integer acc)) xs
  finish := fun acc => .done 16 (.VCon (.Integer acc))
  inspect := inspect compiled
  empty := fun k acc => empty_block kind b callback sem k _
  next := by
    intro k acc a xs n result h
    cases hp : compiled.plan acc a with
    | error m => simp [inspect, inspectPlan, hp] at h
    | done m value =>
      simp [inspect, inspectPlan, hp] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc := compiled.correct acc a xs (callbackStack kind b callback (.VCon (.Integer acc)) a xs ++ k)
      simp only [hp, Plan.map, Plan.Correct] at hc
      rw [preserving_add, preserving_add, before_block, hc]
      exact after_block kind b callback sem k _ _ a xs
  stop := by
    intro k acc a xs n value h
    cases hp : compiled.plan acc a <;> simp [inspect, inspectPlan, hp] at h
  reject := by
    intro k acc a xs n h
    cases hp : compiled.plan acc a with
    | done m value => simp [inspect, inspectPlan, hp] at h
    | error m =>
      simp [inspect, inspectPlan, hp] at h; subst n
      have hc := compiled.correct acc a xs (callbackStack kind b callback (.VCon (.Integer acc)) a xs ++ k)
      simp only [hp, Plan.map, Plan.Correct] at hc
      constructor
      · rw [preserving_add, before_block]; exact hc.1
      · rw [show 25 + m + 1 = 25 + (m + 1) by omega, preserving_add, before_block]
        exact hc.2

/-- Computational summary: no correctness certificate or source CEK term is
    retained in the executable/SMT expression. -/
def dataSummary (kind : Kind) (sem : BuiltinSemanticsVariant)
    (plan : Int → kind.Item → Plan Int) (k : Stack)
    (acc : Int) (xs : List kind.Item) (fuel : Nat) : State :=
  Plan.execute sem k
    (foldPlan (fun n => .done 16 (.VCon (.Integer n))) (inspectPlan plan) acc xs) fuel

def summary (compiled : CompiledCallback kind b callback sem) (k : Stack)
    (acc : Int) (xs : List kind.Item) (fuel : Nat) : State :=
  dataSummary kind sem compiled.plan k acc xs fuel

/-- Carry the generated certificate at the rewrite boundary. -/
def start (_compiled : CompiledCallback kind b callback sem) (k : Stack)
    (acc : Int) (xs : List kind.Item) : State :=
  entry kind b callback k (.VCon (.Integer acc)) xs

theorem run_summary (compiled : CompiledCallback kind b callback sem) (k : Stack)
    (acc : Int) (xs : List kind.Item) (fuel : Nat) :
    runSteps sem (entry kind b callback k (.VCon (.Integer acc)) xs) fuel =
      summary compiled k acc xs fuel :=
  (certificate compiled).run_eq k acc xs fuel

end PlutusCore.UPLC.Optimize.CompiledFold
