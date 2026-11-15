import PlutusCore.UPLC.Optimize.RunSteps

namespace PlutusCore.UPLC.Optimize
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue

/-- A terminating fragment's result and exact CEK cost. `error n` means the
    state after `n` transitions is live and transition `n + 1` fails. This
    convention preserves the distinction between failure and exhausted fuel. -/
inductive Plan (α : Type) where
  | done (cost : Nat) (value : α)
  | error (before : Nat)
deriving Repr, BEq

namespace Plan

def shift (cost : Nat) : Plan α → Plan α
  | .done n v => .done (cost + n) v
  | .error n => .error (cost + n)

def map (f : α → β) : Plan α → Plan β
  | .done n v => .done n (f v)
  | .error n => .error n

/-- Compose summaries without restarting the general CEK evaluator between
    fragments. An earlier error skips the following fragment. -/
def bind (p : Plan α) (next : α → Plan β) : Plan β :=
  match p with
  | .done n v => (next v).shift n
  | .error n => .error n

def execute (sem : BuiltinSemanticsVariant) (k : Stack)
    (p : Plan CekValue) (fuel : Nat) : State :=
  match p with
  | .done n v =>
    if fuel < n then .BudgetExhausted
    else runSteps sem (.Return k v) (fuel - n)
  | .error n => if fuel ≤ n then .BudgetExhausted else .Error

/-- A kernel-checkable certificate at a fragment boundary. No assumptions
    about unused captures, a particular validator, or sufficient fuel occur. -/
def Correct (sem : BuiltinSemanticsVariant) (entry : State) (k : Stack) :
    Plan CekValue → Prop
  | .done n v => runStepsPreservingState sem entry n = .Return k v
  | .error n => Live (runStepsPreservingState sem entry n) ∧
      runStepsPreservingState sem entry (n + 1) = .Error

theorem run_eq (sem : BuiltinSemanticsVariant) (entry : State) (k : Stack)
    (p : Plan CekValue) (h : Correct sem entry k p) (fuel : Nat) :
    runSteps sem entry fuel = execute sem k p fuel := by
  cases p with
  | done n v =>
    change runStepsPreservingState sem entry n = .Return k v at h
    have hl : Live (runStepsPreservingState sem entry n) := by
      rw [h]; trivial
    simpa [execute, h] using runSteps_of_live_prefix sem entry n hl fuel
  | error n =>
    exact runSteps_of_error_prefix sem entry n h.1 h.2 fuel

theorem correct_shift (sem : BuiltinSemanticsVariant) (entry target : State)
    (k : Stack) (cost : Nat) (p : Plan CekValue)
    (block : runStepsPreservingState sem entry cost = target)
    (h : Correct sem target k p) : Correct sem entry k (p.shift cost) := by
  cases p with
  | done n v =>
    change runStepsPreservingState sem entry (cost + n) = .Return k v
    rw [preserving_add, block]; exact h
  | error n =>
    change Live (runStepsPreservingState sem entry (cost + n)) ∧
      runStepsPreservingState sem entry (cost + n + 1) = .Error
    constructor
    · rw [preserving_add, block]; exact h.1
    · rw [show cost + n + 1 = cost + (n + 1) by omega, preserving_add, block]
      exact h.2

/-- Compose arbitrary certified fragments, including error paths. The first
    fragment may have any continuation `middle`; only the second certificate
    needs to explain how that continuation consumes the returned value. -/
theorem correct_bind (sem : BuiltinSemanticsVariant) (entry : State)
    (middle final : Stack) (p : Plan CekValue) (next : CekValue → Plan CekValue)
    (first : Correct sem entry middle p)
    (second : ∀ v, Correct sem (.Return middle v) final (next v)) :
    Correct sem entry final (p.bind next) := by
  cases p with
  | error n => exact first
  | done n v =>
    change runStepsPreservingState sem entry n = .Return middle v at first
    have hs := second v
    cases hn : next v with
    | done m w =>
      simp only [hn, Correct] at hs
      simp only [bind, hn, shift, Correct]
      rw [preserving_add, first]
      exact hs
    | error m =>
      simp only [hn, Correct] at hs
      simp only [bind, hn, shift, Correct]
      constructor
      · rw [preserving_add, first]; exact hs.1
      · rw [show n + m + 1 = n + (m + 1) by omega, preserving_add, first]
        exact hs.2

theorem run_bind (sem : BuiltinSemanticsVariant) (entry : State)
    (middle final : Stack) (p : Plan CekValue) (next : CekValue → Plan CekValue)
    (first : Correct sem entry middle p)
    (second : ∀ v, Correct sem (.Return middle v) final (next v)) (fuel : Nat) :
    runSteps sem entry fuel = execute sem final (p.bind next) fuel :=
  run_eq sem entry final _ (correct_bind sem entry middle final p next first second) fuel

/-- Compose an already summarized fragment with a certified continuation. -/
theorem execute_bind (sem : BuiltinSemanticsVariant) (middle final : Stack)
    (p : Plan CekValue) (next : CekValue → Plan CekValue)
    (h : ∀ v fuel, runSteps sem (.Return middle v) fuel = execute sem final (next v) fuel)
    (fuel : Nat) : execute sem middle p fuel = execute sem final (p.bind next) fuel := by
  cases p with
  | error n => rfl
  | done n v =>
    simp only [execute, bind]
    by_cases hn : fuel < n
    · cases hp : next v <;> simp only [shift, hn, ↓reduceIte]
      · rw [if_pos (by omega)]
      · rw [if_pos (by omega)]
    · rw [if_neg hn, h]
      cases hp : next v with
      | done m w =>
        simp only [shift, execute]
        have bound : fuel - n < m ↔ fuel < n + m := by omega
        simp only [bound, Nat.sub_sub]
      | error m =>
        simp only [shift, execute]
        have bound : fuel - n ≤ m ↔ fuel ≤ n + m := by omega
        simp only [bound]

end Plan
end PlutusCore.UPLC.Optimize
