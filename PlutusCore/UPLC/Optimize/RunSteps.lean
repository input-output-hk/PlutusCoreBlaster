import PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine
open PlutusCore.Default

/-- A state still requiring a CEK transition. -/
def Live : State → Prop
  | .Eval .. | .Return .. => True
  | _ => False

@[simp] theorem preserving_zero (sem : BuiltinSemanticsVariant) (s : State) :
    runStepsPreservingState sem s 0 = s := by cases s <;> rfl

theorem preserving_add (sem : BuiltinSemanticsVariant) (s : State) (a b : Nat) :
    runStepsPreservingState sem s (a + b) =
      runStepsPreservingState sem (runStepsPreservingState sem s a) b := by
  induction a generalizing s with
  | zero => cases s <;> simp [runStepsPreservingState]
  | succ a ih =>
    cases s <;> simp [Nat.succ_add, runStepsPreservingState, ih]

/-- If a finite prefix ends in a live state, execution cannot have halted or
    failed earlier. Fuel below the prefix length therefore exhausts, and fuel
    above it can resume at the prefix's last state. -/
theorem runSteps_of_live_prefix (sem : BuiltinSemanticsVariant) (s : State)
    (m : Nat) (h : Live (runStepsPreservingState sem s m)) (n : Nat) :
    runSteps sem s n =
      if n < m then .BudgetExhausted
      else runSteps sem (runStepsPreservingState sem s m) (n - m) := by
  induction m generalizing s n with
  | zero => cases s <;> simp_all [runStepsPreservingState, Live]
  | succ m ih =>
    cases s with
    | Eval k env t =>
      cases n with
      | zero => simp [runSteps]
      | succ n =>
        simpa only [runStepsPreservingState, runSteps, Nat.succ_lt_succ_iff,
          Nat.succ_sub_succ_eq_sub] using ih (step sem (.Eval k env t)) h n
    | Return k v =>
      cases n with
      | zero => simp [runSteps]
      | succ n =>
        simpa only [runStepsPreservingState, runSteps, Nat.succ_lt_succ_iff,
          Nat.succ_sub_succ_eq_sub] using ih (step sem (.Return k v)) h n
    | Error => simp [runStepsPreservingState, Live] at h
    | BudgetExhausted => simp [runStepsPreservingState, Live] at h
    | Halt v => simp [runStepsPreservingState, Live] at h

theorem runSteps_of_error_prefix (sem : BuiltinSemanticsVariant) (s : State)
    (m : Nat) (h : Live (runStepsPreservingState sem s m))
    (he : runStepsPreservingState sem s (m + 1) = .Error) (n : Nat) :
    runSteps sem s n = if n ≤ m then .BudgetExhausted else .Error := by
  have hs : step sem (runStepsPreservingState sem s m) = .Error := by
    rw [preserving_add] at he
    cases ht : runStepsPreservingState sem s m <;>
      simp_all [Live, runStepsPreservingState]
  rw [runSteps_of_live_prefix sem s m h n]
  split
  next hn => simp [show n ≤ m by omega]
  next hn =>
    cases hr : n - m with
    | zero =>
      have hnm : n = m := by omega
      subst n
      cases ht : runStepsPreservingState sem s m <;>
        simp_all [Live, runSteps]
    | succ r =>
      have hnm : ¬ n ≤ m := by omega
      cases ht : runStepsPreservingState sem s m <;>
        simp_all [Live, runSteps]

end PlutusCore.UPLC.CekMachine
