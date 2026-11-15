import PlutusCore.UPLC.Optimize.Plan

namespace PlutusCore.UPLC.Optimize
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue

/-- A successful iteration descends into the tail and later reconstructs a
    result; a rejected element fails without inspecting the tail. Costs may
    depend on the element and on any parameters captured by `inspect`. -/
inductive TraversalStep where
  | descend (before after : Nat)
  | reject (before : Nat)
deriving Repr, BEq

def traversalPlan (render : List α → CekValue) (nilCost : Nat)
    (inspect : α → TraversalStep) : List α → Plan CekValue
  | [] => .done nilCost (render [])
  | a :: xs =>
    match inspect a with
    | .reject n => .error n
    | .descend before after =>
      match traversalPlan render nilCost inspect xs with
      | .done n _ => .done (before + n + after) (render (a :: xs))
      | .error n => .error (before + n)

theorem traversalPlan_done_value (render : List α → CekValue) (nilCost : Nat)
    (inspect : α → TraversalStep) (xs : List α) (n : Nat) (v : CekValue)
    (h : traversalPlan render nilCost inspect xs = .done n v) : v = render xs := by
  cases xs with
  | nil => simp [traversalPlan] at h; exact h.2.symm
  | cons a xs =>
    cases hi : inspect a with
    | reject before => simp [traversalPlan, hi] at h
    | descend before after =>
      cases ht : traversalPlan render nilCost inspect xs <;>
        simp [traversalPlan, hi, ht] at h
      exact h.2.symm

/-- Expose a traversal's known result shape instead of forgetting it behind
    an arbitrary `CekValue` returned by a recursive cost computation. -/
def executeTraversal (sem : BuiltinSemanticsVariant) (k : Stack)
    (render : List α → CekValue) (nilCost : Nat) (inspect : α → TraversalStep)
    (xs : List α) (fuel : Nat) : State :=
  match traversalPlan render nilCost inspect xs with
  | .done n _ => if fuel < n then .BudgetExhausted else
      runSteps sem (.Return k (render xs)) (fuel - n)
  | .error n => if fuel ≤ n then .BudgetExhausted else .Error

theorem execute_traversal (sem : BuiltinSemanticsVariant) (k : Stack)
    (render : List α → CekValue) (nilCost : Nat) (inspect : α → TraversalStep)
    (xs : List α) (fuel : Nat) :
    Plan.execute sem k (traversalPlan render nilCost inspect xs) fuel =
      executeTraversal sem k render nilCost inspect xs fuel := by
  cases hp : traversalPlan render nilCost inspect xs with
  | done n v =>
    have hv := traversalPlan_done_value render nilCost inspect xs n v hp
    simp [Plan.execute, executeTraversal, hp, hv]
  | error n => simp [Plan.execute, executeTraversal, hp]

/-- A compiler adapter proves only the bounded empty/one-iteration/unwind
    blocks. The unbounded induction and all finite-fuel cases are shared. -/
structure Traversal (sem : BuiltinSemanticsVariant) (α : Type) where
  entry : Stack → List α → State
  render : List α → CekValue
  frame : α → Frame
  nilCost : Nat
  inspect : α → TraversalStep
  empty : ∀ k, runStepsPreservingState sem (entry k []) nilCost = .Return k (render [])
  descend : ∀ k a xs before after, inspect a = .descend before after →
    runStepsPreservingState sem (entry k (a :: xs)) before = entry (frame a :: k) xs
  unwind : ∀ k a xs before after, inspect a = .descend before after →
    runStepsPreservingState sem (.Return (frame a :: k) (render xs)) after =
      .Return k (render (a :: xs))
  reject : ∀ k a xs n, inspect a = .reject n →
    Live (runStepsPreservingState sem (entry k (a :: xs)) n) ∧
      runStepsPreservingState sem (entry k (a :: xs)) (n + 1) = .Error

namespace Traversal

def plan (spec : Traversal sem α) (xs : List α) : Plan CekValue :=
  traversalPlan spec.render spec.nilCost spec.inspect xs

theorem correct (spec : Traversal sem α) (k : Stack) (xs : List α) :
    Plan.Correct sem (spec.entry k xs) k (spec.plan xs) := by
  induction xs generalizing k with
  | nil => exact spec.empty k
  | cons a xs ih =>
    cases hi : spec.inspect a with
    | reject n =>
      simpa only [plan, traversalPlan, hi, Plan.Correct] using spec.reject k a xs n hi
    | descend before after =>
      have head := spec.descend k a xs before after hi
      have tail := ih (spec.frame a :: k)
      cases hp : spec.plan xs with
      | done n v =>
        have hp' : traversalPlan spec.render spec.nilCost spec.inspect xs = .done n v := hp
        have value := traversalPlan_done_value spec.render spec.nilCost spec.inspect xs n v hp'
        subst v
        simp only [hp, Plan.Correct] at tail
        simp only [plan, traversalPlan, hi, hp', Plan.Correct]
        rw [preserving_add, preserving_add, head, tail]
        exact spec.unwind k a xs before after hi
      | error n =>
        have hp' : traversalPlan spec.render spec.nilCost spec.inspect xs = .error n := hp
        simp only [hp, Plan.Correct] at tail
        simp only [plan, traversalPlan, hi, hp', Plan.Correct]
        constructor
        · rw [preserving_add, head]; exact tail.1
        · rw [show before + n + 1 = before + (n + 1) by omega, preserving_add, head]
          exact tail.2

theorem run_eq (spec : Traversal sem α) (k : Stack) (xs : List α) (fuel : Nat) :
    runSteps sem (spec.entry k xs) fuel = Plan.execute sem k (spec.plan xs) fuel :=
  Plan.run_eq sem _ k _ (spec.correct k xs) fuel

end Traversal

/-- A search can return at the first match, continue on the tail, or reject
    an invalid element. Its element operation is independent of the tail. -/
inductive SearchStep where
  | found (cost : Nat)
  | next (cost : Nat)
  | reject (before : Nat)
deriving Repr, BEq

def searchPlan (render : Option α → CekValue) (nilCost : Nat)
    (inspect : α → SearchStep) : List α → Plan CekValue
  | [] => .done nilCost (render none)
  | a :: xs =>
    match inspect a with
    | .found n => .done n (render (some a))
    | .next n => (searchPlan render nilCost inspect xs).shift n
    | .reject n => .error n

structure Search (sem : BuiltinSemanticsVariant) (α : Type) where
  entry : Stack → List α → State
  render : Option α → CekValue
  nilCost : Nat
  inspect : α → SearchStep
  empty : ∀ k, runStepsPreservingState sem (entry k []) nilCost = .Return k (render none)
  found : ∀ k a xs n, inspect a = .found n →
    runStepsPreservingState sem (entry k (a :: xs)) n = .Return k (render (some a))
  next : ∀ k a xs n, inspect a = .next n →
    runStepsPreservingState sem (entry k (a :: xs)) n = entry k xs
  reject : ∀ k a xs n, inspect a = .reject n →
    Live (runStepsPreservingState sem (entry k (a :: xs)) n) ∧
      runStepsPreservingState sem (entry k (a :: xs)) (n + 1) = .Error

namespace Search

def plan (spec : Search sem α) (xs : List α) : Plan CekValue :=
  searchPlan spec.render spec.nilCost spec.inspect xs

theorem correct (spec : Search sem α) (k : Stack) (xs : List α) :
    Plan.Correct sem (spec.entry k xs) k (spec.plan xs) := by
  induction xs generalizing k with
  | nil => exact spec.empty k
  | cons a xs ih =>
    cases hi : spec.inspect a with
    | found n =>
      simpa only [plan, searchPlan, hi, Plan.Correct] using spec.found k a xs n hi
    | next n =>
      simpa only [plan, searchPlan, hi] using
        Plan.correct_shift sem _ _ k n _ (spec.next k a xs n hi) (ih k)
    | reject n =>
      simpa only [plan, searchPlan, hi, Plan.Correct] using spec.reject k a xs n hi

theorem run_eq (spec : Search sem α) (k : Stack) (xs : List α) (fuel : Nat) :
    runSteps sem (spec.entry k xs) fuel = Plan.execute sem k (spec.plan xs) fuel :=
  Plan.run_eq sem _ k _ (spec.correct k xs) fuel

end Search
end PlutusCore.UPLC.Optimize
