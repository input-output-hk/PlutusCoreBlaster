import PlutusCore.UPLC.CekMachine.Lemmas

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue Environment)
open PlutusCore.UPLC.Term (BuiltinFun Const Term)
open PlutusCore.UPLC.ExBudget (ExBudget)

/-! ## Theorems on appending to the stack of a CEK state. -/

/-- Appends `s` to the stack of an `Eval` or `Return` state. -/
def appendStack (s : Stack) : State → State
  | .Eval st rho t => .Eval (st ++ s) rho t
  | .Return st V => .Return (st ++ s) V
  | .Error => .Error
  | .Halt V => .Halt V

/-- `step` commutes with `appendStack s` on every state other than a `Return` with an empty
stack. -/
theorem step_appendStack (sv : BuiltinSemanticsVariant) (s : Stack) (Sigma : State)
    (hne : ∀ V, Sigma ≠ State.Return [] V) :
    step sv (appendStack s Sigma) = appendStack s (step sv Sigma) := by
  have hfold : ∀ xs st, step.folding xs (st ++ s) = step.folding xs st ++ s := by
    intro xs st; induction xs <;> simp_all [step.folding]
  match Sigma, hne with
  | .Error, _ | .Halt _, _ => rfl
  | .Return [] V, hne => exact absurd rfl (hne V)
  | .Eval _ _ _, _ | .Return (_ :: _) _, _ =>
      simp only [step, evalBuiltin, appendStack.eq_1, appendStack.eq_2, List.cons_append] <;>
        (repeat' split) <;> simp_all [appendStack]

/-- Appending `s` to the starting stack of a costed run that has not halted after `n` steps appends
`s` to its state after `n` steps and leaves its costs and builtin calls unchanged. -/
theorem runStepsCosting_appendStack (sv : BuiltinSemanticsVariant) (s : Stack) :
    ∀ (n : Nat) (Sigma : State) (stepCost : ExBudget)
      (calls : List (BuiltinFun × List CekValue)), (∀ W, stepN sv Sigma n ≠ State.Halt W) →
      runStepsCosting sv (appendStack s Sigma) n stepCost calls =
        (appendStack s (stepN sv Sigma n), (runStepsCosting sv Sigma n stepCost calls).2)
  | 0, Sigma, _, _, _ => by cases Sigma <;> rfl
  | n + 1, Sigma, stepCost, calls, h => by
      have hne : ∀ W, Sigma ≠ State.Return [] W := by
        rintro W rfl
        exact h W (stepN_of_terminal sv _ (Or.inl ⟨W, rfl⟩) n)
      have ih := runStepsCosting_appendStack sv s n (step sv Sigma)
        (stepCost + calculateStepCostr (semVarToCosts sv) Sigma)
        (match saturatedBuiltin? Sigma with | some call => call :: calls | none => calls) h
      match Sigma, hne with
      | .Error, _ | .Halt _, _ => simp [runStepsCosting, appendStack]
      | .Return [] V, hne => exact absurd rfl (hne V)
      | .Eval _ _ t, hne => rw [← step_appendStack sv s _ hne] at ih; cases t <;> exact ih
      | .Return (_ :: _) _, hne => rw [← step_appendStack sv s _ hne] at ih; exact ih

/-- Appending `s` to the starting stack of a run that has not halted after `n` steps appends `s`
to its state after `n` steps. -/
theorem stepN_appendStack (sv : BuiltinSemanticsVariant) (s : Stack) (n : Nat) (Sigma : State)
    (h : ∀ W, stepN sv Sigma n ≠ State.Halt W) :
    stepN sv (appendStack s Sigma) n = appendStack s (stepN sv Sigma n) := by
  rw [← runStepsCosting_fst sv _ n ExBudget.zero [],
    runStepsCosting_appendStack sv s n Sigma _ _ h]

/-- A term whose run from the empty stack is at `State.Return [] V` after `n` steps is at
`State.Return s V` after `n` steps from any stack `s`. -/
theorem stepN_stack_independent (sv : BuiltinSemanticsVariant) (rho : Environment) (T : Term)
    (s : Stack) (n : Nat) (V : CekValue)
    (h : stepN sv (State.Eval [] rho T) n = State.Return [] V) :
    stepN sv (State.Eval s rho T) n = State.Return s V := by
  simpa [h, appendStack] using stepN_appendStack sv s n (State.Eval [] rho T) (by simp [h])

/-- A term whose costed run from the empty stack is at `State.Return [] V` after `n` steps at cost
`c` is at `State.Return s V` after `n` steps at cost `c` from any stack `s`. -/
theorem runStepsWithCost_stack_independent (sv : BuiltinSemanticsVariant) (rho : Environment)
    (T : Term) (s : Stack) (n : Nat) (V : CekValue) (c : ExBudget)
    (h : runStepsWithCost sv (State.Eval [] rho T) n = (State.Return [] V, c)) :
    runStepsWithCost sv (State.Eval s rho T) n = (State.Return s V, c) := by
  simp only [runStepsWithCost, Prod.mk.injEq, runStepsCosting_fst] at h
  have := runStepsCosting_appendStack sv s n (State.Eval [] rho T) ExBudget.zero [] (by simp [h.1])
  simp_all [runStepsWithCost, appendStack]

/-- A term whose run from the empty stack halts at `V` within `n` steps is at `State.Return s V`
after fewer than `n` steps from any stack `s`. -/
theorem runSteps_stack_independent (sv : BuiltinSemanticsVariant) (rho : Environment) (T : Term)
    (s : Stack) (n : Nat) (V : CekValue)
    (h : runSteps sv (State.Eval [] rho T) n = State.Halt V) :
    ∃ k < n, stepN sv (State.Eval s rho T) k = State.Return s V := by
  suffices hret : ∀ n Sigma, (∀ W, Sigma ≠ State.Halt W) →
      runSteps sv Sigma n = State.Halt V → ∃ k < n, stepN sv Sigma k = State.Return [] V by
    obtain ⟨k, hk, hk'⟩ := hret n _ (fun _ => State.noConfusion) h
    exact ⟨k, hk, stepN_stack_independent sv rho T s k V hk'⟩
  intro n
  induction n with
  | zero => intro Sigma hs h; cases Sigma <;> simp_all [runSteps]
  | succ n ih =>
      intro Sigma hs h
      match Sigma, hs with
      | .Halt _, _ | .Error, _ => simp_all [runSteps]
      | .Return [] W, _ => exact ⟨0, by omega, by simp_all [runSteps, step, stepN]⟩
      | .Eval _ _ _, _ | .Return (_ :: _) _, _ =>
          obtain ⟨k, hk, hk'⟩ := ih _ (fun W hW => by
            simp only [step, evalBuiltin] at hW; (repeat' split at hW) <;> cases hW) h
          exact ⟨k + 1, by omega, hk'⟩

/-- A term whose costed run from the empty stack halts at `V` within `n` steps at cost `c` is at
`State.Return s V` after fewer than `n` steps at cost `c` from any stack `s`. -/
theorem runStepsWithCost_halt_stack_independent (sv : BuiltinSemanticsVariant)
    (rho : Environment) (T : Term) (s : Stack) (n : Nat) (V : CekValue) (c : ExBudget)
    (h : runStepsWithCost sv (State.Eval [] rho T) n = (State.Halt V, c)) :
    ∃ k < n, runStepsWithCost sv (State.Eval s rho T) k = (State.Return s V, c) := by
  obtain ⟨k, hk, hk'⟩ := runSteps_stack_independent sv rho T [] n V
    ((runSteps_halt_iff_runStepsWithCost sv _ V n).2 (by rw [h]))
  have h1 : (runStepsWithCost sv (State.Eval [] rho T) k).1 = State.Return [] V := by
    rw [runStepsWithCost_fst, hk']
  obtain ⟨m, rfl⟩ : ∃ m, n = k + (m + 1) := ⟨n - k - 1, by omega⟩
  rw [runStepsWithCost_add, h1] at h
  have hr : runStepsWithCost sv (State.Return [] V) (m + 1) = (State.Halt V, ExBudget.zero) := by
    cases m <;> simp [runStepsWithCost, runStepsCosting, step, calculateStepCostr,
      saturatedBuiltin?, builtinCallsCost]
  rw [hr, Prod.mk.injEq] at h
  refine ⟨k, hk, runStepsWithCost_stack_independent sv rho T s k V c ?_⟩
  exact Prod.ext h1 (by simpa using h.2)

end PlutusCore.UPLC.CekMachine
