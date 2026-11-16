import PlutusCore.UPLC.Optimize.Plan

namespace PlutusCore.UPLC.Optimize
open PlutusCore.Default PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue

/-- A callback may update an accumulator or stop the traversal early. Its
    exact cost and possible failure are carried by the surrounding Plan. -/
inductive FoldControl (σ β : Type) where
  | next (acc : σ)
  | stop (result : β)

/-- Stateful, short-circuiting fold. The same recursion handles lengths,
    sums, searches, validation and nested callbacks; no field is hardcoded. -/
def foldPlan (finish : σ → Plan β) (inspect : σ → α → Plan (FoldControl σ β)) :
    σ → List α → Plan β
  | acc, [] => finish acc
  | acc, a :: xs =>
    match inspect acc a with
    | .error n => .error n
    | .done n (.stop v) => .done n v
    | .done n (.next acc') => (foldPlan finish inspect acc' xs).shift n

/-- A compiler adapter certifies only one iteration. Induction over arbitrary
    lists, exact failure boundaries and all finite fuel cases are shared. -/
structure Fold (sem : BuiltinSemanticsVariant) (α σ : Type) where
  entry : Stack → σ → List α → State
  finish : σ → Plan CekValue
  inspect : σ → α → Plan (FoldControl σ CekValue)
  empty : ∀ k acc, Plan.Correct sem (entry k acc []) k (finish acc)
  next : ∀ k acc a xs n acc', inspect acc a = .done n (.next acc') →
    runStepsPreservingState sem (entry k acc (a :: xs)) n = entry k acc' xs
  stop : ∀ k acc a xs n v, inspect acc a = .done n (.stop v) →
    Plan.Correct sem (entry k acc (a :: xs)) k (.done n v)
  reject : ∀ k acc a xs n, inspect acc a = .error n →
    Plan.Correct sem (entry k acc (a :: xs)) k (.error n)

namespace Fold

def plan (spec : Fold sem α σ) (acc : σ) (xs : List α) : Plan CekValue :=
  foldPlan spec.finish spec.inspect acc xs

theorem correct (spec : Fold sem α σ) (k : Stack) (acc : σ) (xs : List α) :
    Plan.Correct sem (spec.entry k acc xs) k (spec.plan acc xs) := by
  induction xs generalizing acc with
  | nil => exact spec.empty k acc
  | cons a xs ih =>
    cases hi : spec.inspect acc a with
    | error n =>
      simpa only [plan, foldPlan, hi] using spec.reject k acc a xs n hi
    | done n control =>
      cases control with
      | stop v =>
        simpa only [plan, foldPlan, hi] using spec.stop k acc a xs n v hi
      | next acc' =>
        simpa only [plan, foldPlan, hi] using
          Plan.correct_shift sem _ _ k n _ (spec.next k acc a xs n acc' hi) (ih acc')

theorem run_eq (spec : Fold sem α σ) (k : Stack) (acc : σ) (xs : List α) (fuel : Nat) :
    runSteps sem (spec.entry k acc xs) fuel = Plan.execute sem k (spec.plan acc xs) fuel :=
  Plan.run_eq sem _ k _ (spec.correct k acc xs) fuel

end Fold

/-- The pure foldLeft case has one common value/cost theorem. Callbacks may
    still be composed with nested plans before providing these equations. -/
theorem foldPlan_foldl (update : σ → α → σ) (render : σ → β)
    (nilCost stepCost : Nat) (acc : σ) (xs : List α) :
    foldPlan (fun s => .done nilCost (render s))
      (fun s a => .done stepCost (.next (update s a))) acc xs =
      .done (xs.length * stepCost + nilCost) (render (xs.foldl update acc)) := by
  induction xs generalizing acc with
  | nil => simp [foldPlan]
  | cons a xs ih =>
    simp only [foldPlan, ih, Plan.shift, List.length_cons, List.foldl_cons,
      Nat.add_mul, Nat.one_mul]
    congr 1
    omega

end PlutusCore.UPLC.Optimize
