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

/-- A costed run at `State.Return [] V` after `n` steps at cost `c` is at `State.Return s V` after
`n` steps at cost `c` with `s` appended to its starting stack. -/
theorem runStepsWithCost_appendStack_return (sv : BuiltinSemanticsVariant) (s : Stack)
    (Sigma : State) (n : Nat) (V : CekValue) (c : ExBudget)
    (h : runStepsWithCost sv Sigma n = (State.Return [] V, c)) :
    runStepsWithCost sv (appendStack s Sigma) n = (State.Return s V, c) := by
  simp only [runStepsWithCost, Prod.mk.injEq, runStepsCosting_fst] at h
  have := runStepsCosting_appendStack sv s n Sigma ExBudget.zero [] (by simp [h.1])
  simp_all [runStepsWithCost, appendStack]

/-- A term whose costed run from the empty stack is at `State.Return [] V` after `n` steps at cost
`c` is at `State.Return s V` after `n` steps at cost `c` from any stack `s`. -/
theorem runStepsWithCost_stack_independent (sv : BuiltinSemanticsVariant) (rho : Environment)
    (T : Term) (s : Stack) (n : Nat) (V : CekValue) (c : ExBudget)
    (h : runStepsWithCost sv (State.Eval [] rho T) n = (State.Return [] V, c)) :
    runStepsWithCost sv (State.Eval s rho T) n = (State.Return s V, c) :=
  runStepsWithCost_appendStack_return sv s _ n V c h

/-- Only `Return []` and `Halt` states step to a `Halt` state. -/
theorem step_eq_halt (sv : BuiltinSemanticsVariant) (Sigma : State) (W : CekValue)
    (h : step sv Sigma = State.Halt W) : Sigma = State.Return [] W ∨ Sigma = State.Halt W := by
  match Sigma with
  | .Halt V => simp_all [step]
  | .Error => simp [step] at h
  | .Return [] V => left; simp_all [step]
  | .Eval _ _ _ | .Return (_ :: _) _ =>
      exfalso; simp only [step, evalBuiltin] at h; (repeat' split at h) <;> cases h

/-- A run from a state other than a halt that is at no `Return []` state before `n` steps is not
halted after `n` steps. -/
theorem stepN_not_halt_of_no_return (sv : BuiltinSemanticsVariant) (Sigma : State)
    (hSigma : ∀ W, Sigma ≠ State.Halt W) (n : Nat)
    (hno : ∀ k < n, ∀ V, stepN sv Sigma k ≠ State.Return [] V) :
    ∀ W, stepN sv Sigma n ≠ State.Halt W := by
  induction n with
  | zero => exact hSigma
  | succ n ih =>
      intro W h
      rw [stepN_add] at h
      rcases step_eq_halt sv _ W (by simpa [stepN] using h) with h2 | h2
      · exact hno n (by omega) W h2
      · exact ih (fun k hk V => hno k (by omega) V) W h2

/-- The costed run from a state `Sigma` other than a halt with `s` appended to its stack halts at
`W` within `n` steps at cost `c` exactly when the run from `Sigma` returns some `V` after `k ≤ n`
steps at cost `c1` and the run from `State.Return s V` halts at `W` in the remaining steps at cost
`c2`, with `c = c1 + c2`. -/
theorem runStepsWithCost_appendStack_halt_iff (sv : BuiltinSemanticsVariant) (s : Stack)
    (Sigma : State) (hSigma : ∀ W, Sigma ≠ State.Halt W) (n : Nat) (W : CekValue) (c : ExBudget) :
    runStepsWithCost sv (appendStack s Sigma) n = (State.Halt W, c) ↔
      ∃ k V c1 c2, k ≤ n ∧ runStepsWithCost sv Sigma k = (State.Return [] V, c1) ∧
        runStepsWithCost sv (State.Return s V) (n - k) = (State.Halt W, c2) ∧ c = c1 + c2 := by
  constructor
  · intro h
    have hex : ∃ k < n, ∃ V, stepN sv Sigma k = State.Return [] V := by
      refine Classical.byContradiction fun hno => ?_
      have hnh := stepN_not_halt_of_no_return sv Sigma hSigma n
        (fun k hk V hV => hno ⟨k, hk, V, hV⟩)
      have hs := stepN_appendStack sv s n Sigma hnh
      rw [← runStepsWithCost_fst, h] at hs
      revert hs hnh
      cases stepN sv Sigma n <;> simp [appendStack]
    obtain ⟨k, hk, V, hV⟩ := hex
    have hk1 : runStepsWithCost sv Sigma k = (State.Return [] V, (runStepsWithCost sv Sigma k).2) :=
      Prod.ext (by rw [runStepsWithCost_fst, hV]) rfl
    obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
    rw [runStepsWithCost_add, runStepsWithCost_appendStack_return sv s Sigma k V _ hk1,
      Prod.mk.injEq] at h
    refine ⟨k, V, _, _, by omega, hk1, ?_, h.2.symm⟩
    simp only [Nat.add_sub_cancel_left]
    exact Prod.ext h.1 rfl
  · rintro ⟨k, V, c1, c2, hk, h1, h2, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
    simp only [Nat.add_sub_cancel_left] at h2
    rw [runStepsWithCost_add, runStepsWithCost_appendStack_return sv s Sigma k V c1 h1, h2]

/-- The costed run of `T` on stack `s` halts at `W` within `n` steps at cost `c` exactly when its
run on the empty stack returns some `V` after `k ≤ n` steps at cost `c1` and the run from
`State.Return s V` halts at `W` in the remaining steps at cost `c2`, with `c = c1 + c2`. -/
theorem runStepsWithCost_halt_iff_split (sv : BuiltinSemanticsVariant) (rho : Environment)
    (T : Term) (s : Stack) (n : Nat) (W : CekValue) (c : ExBudget) :
    runStepsWithCost sv (State.Eval s rho T) n = (State.Halt W, c) ↔
      ∃ k V c1 c2, k ≤ n ∧
        runStepsWithCost sv (State.Eval [] rho T) k = (State.Return [] V, c1) ∧
        runStepsWithCost sv (State.Return s V) (n - k) = (State.Halt W, c2) ∧ c = c1 + c2 :=
  runStepsWithCost_appendStack_halt_iff sv s (State.Eval [] rho T) (fun _ h => by cases h) n W c

/-- A term whose costed run from the empty stack halts at `V` within `n` steps at cost `c` is at
`State.Return s V` after fewer than `n` steps at cost `c` from any stack `s`. -/
theorem runStepsWithCost_halt_stack_independent (sv : BuiltinSemanticsVariant)
    (rho : Environment) (T : Term) (s : Stack) (n : Nat) (V : CekValue) (c : ExBudget)
    (h : runStepsWithCost sv (State.Eval [] rho T) n = (State.Halt V, c)) :
    ∃ k < n, runStepsWithCost sv (State.Eval s rho T) k = (State.Return s V, c) := by
  obtain ⟨k, W, c1, c2, hk, h1, h2, rfl⟩ := (runStepsWithCost_halt_iff_split sv rho T [] n V c).1 h
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := by
    cases hnk : n - k with
    | zero => rw [hnk] at h2; cases h2
    | succ m => exact ⟨m, rfl⟩
  rw [hm] at h2
  have hr : runStepsWithCost sv (State.Return [] W) (m + 1) = (State.Halt W, ExBudget.zero) := by
    cases m <;> simp [runStepsWithCost, runStepsCosting, step, calculateStepCostr,
      saturatedBuiltin?, builtinCallsCost]
  rw [hr, Prod.mk.injEq, State.Halt.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  exact ⟨k, by omega, by simpa using runStepsWithCost_stack_independent sv rho T s k W c1 h1⟩

end PlutusCore.UPLC.CekMachine
