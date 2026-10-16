import PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Term (Program Term BuiltinFun)
open PlutusCore.UPLC.ExBudget (ExBudget)

/-! ## Theorems on iteration of the CEK `step` function. -/

/-! ### Iteration of `step` -/

def stepN (sv : BuiltinSemanticsVariant) (s : State) : Nat → State
  | 0 => s
  | (n + 1) => stepN sv (step sv s) n

/-! ### Terminal states -/

/-- A state the machine stops on. -/
def terminal (s : State) : Prop := (∃ V, s = State.Halt V) ∨ s = State.Error

instance : DecidablePred terminal := fun s =>
  match s with
  | State.Halt V => isTrue (Or.inl ⟨V, rfl⟩)
  | State.Error => isTrue (Or.inr rfl)
  | State.Eval _ _ _ => isFalse (by rintro (⟨V, h⟩ | h) <;> cases h)
  | State.Return _ _ => isFalse (by rintro (⟨V, h⟩ | h) <;> cases h)

/-- `step` fixes exactly the terminal states. -/
theorem step_fix_iff (sv : BuiltinSemanticsVariant) (s : State) :
    step sv s = s ↔ terminal s := by
  refine ⟨fun h => ?_, fun h => by rcases h with ⟨V, rfl⟩ | rfl <;> rfl⟩
  cases s with
  | Halt V => exact Or.inl ⟨V, rfl⟩
  | Error => exact Or.inr rfl
  | Eval st rho t => exact absurd h (by cases t <;> simp only [step] <;> (try split) <;> simp_all)
  | Return st v =>
      exact absurd h (by
        cases st <;> (try (rename_i f _; cases f)) <;> (try cases v) <;>
          simp only [step, evalBuiltin] <;> (repeat' split) <;> simp_all)

/-! ### Fuel composition -/

/-- Fuel composition for `stepN`, with no side condition. -/
theorem stepN_add (sv : BuiltinSemanticsVariant) (s : State) (n m : Nat) :
    stepN sv s (n + m) = stepN sv (stepN sv s n) m := by
  induction n generalizing s with
  | zero => simp [stepN]
  | succ p ih => rw [Nat.succ_add]; exact ih (step sv s)

/-- A terminal state is the state at every index of the run from it. -/
theorem stepN_of_terminal (sv : BuiltinSemanticsVariant) (s : State) (h : terminal s)
    (n : Nat) : stepN sv s n = s := by
  induction n with
  | zero => rfl
  | succ p ih =>
      show stepN sv (step sv s) p = s
      rw [(step_fix_iff sv s).mpr h]
      exact ih

/-- A run whose state at `n` is terminal is at that state at every index past `n`. -/
theorem stepN_fix (sv : BuiltinSemanticsVariant) (s : State) (n : Nat)
    (h : terminal (stepN sv s n)) (m : Nat) :
    stepN sv s (n + m) = stepN sv s n := by
  rw [stepN_add]
  exact stepN_of_terminal sv _ h m

/-! ### `runSteps` in terms of `stepN` -/

/-- `runSteps` returns the state at index `n` when that state is a `Halt` state, and
`State.Error` otherwise. -/
theorem runSteps_eq_stepN (sv : BuiltinSemanticsVariant) (s : State) (n : Nat) :
    runSteps sv s n =
      match stepN sv s n with
      | State.Halt V => State.Halt V
      | _ => State.Error := by
  induction n generalizing s with
  | zero => cases s <;> rfl
  | succ p ih =>
      cases s with
      | Halt V => rw [stepN_of_terminal sv _ (Or.inl ⟨V, rfl⟩)]; rfl
      | Error => rw [stepN_of_terminal sv _ (Or.inr rfl)]; rfl
      | Eval st rho t => exact ih (step sv (State.Eval st rho t))
      | Return st v => exact ih (step sv (State.Return st v))

/-! ### Program execution -/

/-- A program's halt result does not depend on how much fuel it was given, past enough. -/
theorem cekExecuteProgramWithSemanticVariant_halt_stable
    (sv : BuiltinSemanticsVariant) (p : Program) (params : List Term) (V : CekValue) (n m : Nat)
    (h : cekExecuteProgramWithSemanticVariant sv p params n = State.Halt V) :
    cekExecuteProgramWithSemanticVariant sv p params (n + m) = State.Halt V := by
  cases p with
  | Program ver body =>
      simp only [cekExecuteProgramWithSemanticVariant, runSteps_eq_stepN] at h ⊢
      have hs : stepN sv (initialState (applyParams body params)) n = State.Halt V := by
        split at h <;> simp_all
      rw [stepN_fix sv _ n (Or.inl ⟨V, hs⟩) m, hs]

@[simp] theorem stepN_halt (sv : BuiltinSemanticsVariant) (V : CekValue) (n : Nat) :
    stepN sv (State.Halt V) n = State.Halt V := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [stepN, stepAbs] using ih

@[simp] theorem stepN_error (sv : BuiltinSemanticsVariant) (n : Nat) :
    stepN sv State.Error n = State.Error := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [stepN, stepAbs] using ih

/-! ## Costs  -/

theorem builtinCallsCost_append (sv : BuiltinSemanticsVariant)
    (l₁ l₂ : List (BuiltinFun × List CekValue)) :
    builtinCallsCost sv (l₁ ++ l₂) = builtinCallsCost sv l₁ + builtinCallsCost sv l₂ := by
  induction l₁ with
  | nil => simp [builtinCallsCost]
  | cons c cs ih =>
      obtain ⟨b, args⟩ := c
      simp only [List.cons_append, builtinCallsCost, ih, ExBudget.add_assoc]

/-- The accumulators of `runStepsCosting` only accumulate. -/
theorem runStepsCosting_acc (sv : BuiltinSemanticsVariant) (s : State) (n : Nat)
    (stepCost : ExBudget) (calls : List (BuiltinFun × List CekValue)) :
    runStepsCosting sv s n stepCost calls =
      ((runStepsCosting sv s n ExBudget.zero []).1,
       stepCost + (runStepsCosting sv s n ExBudget.zero []).2.1,
       (runStepsCosting sv s n ExBudget.zero []).2.2 ++ calls) := by
  induction n generalizing s stepCost calls with
  | zero => cases s <;> simp [runStepsCosting]
  | succ n ih =>
      cases s with
      | Halt V => simp [runStepsCosting]
      | Error => simp [runStepsCosting]
      | Eval st rho t =>
          simp only [runStepsCosting]
          rw [ih _ (stepCost + _), ih _ (ExBudget.zero + _)]
          cases saturatedBuiltin? (State.Eval st rho t) <;>
            simp [ExBudget.add_assoc]
      | Return st v =>
          simp only [runStepsCosting]
          rw [ih _ (stepCost + _), ih _ (ExBudget.zero + _)]
          cases saturatedBuiltin? (State.Return st v) <;>
            simp [ExBudget.add_assoc]

/-- The costed run reaches the state `stepN` reaches. -/
theorem runStepsCosting_fst (sv : BuiltinSemanticsVariant) (s : State) (n : Nat)
    (stepCost : ExBudget) (calls : List (BuiltinFun × List CekValue)) :
    (runStepsCosting sv s n stepCost calls).1 = stepN sv s n := by
  induction n generalizing s stepCost calls with
  | zero => cases s <;> rfl
  | succ n ih =>
      cases s with
      | Halt V =>
          simp only [runStepsCosting, stepN, stepAbs]
          exact (stepN_halt sv V n).symm
      | Error =>
          simp only [runStepsCosting, stepN, stepAbs]
          exact (stepN_error sv n).symm
      | Eval st rho t => simp only [runStepsCosting, stepN, stepAbs]; exact ih _ _ _
      | Return st v => simp only [runStepsCosting, stepN, stepAbs]; exact ih _ _ _

theorem runStepsWithCost_fst (sv : BuiltinSemanticsVariant) (s : State) (n : Nat) :
    (runStepsWithCost sv s n).1 = stepN sv s n :=
  runStepsCosting_fst sv s n _ _

/-- Costing changes nothing about where a run halts. -/
theorem runSteps_halt_iff_runStepsWithCost (sv : BuiltinSemanticsVariant) (s : State)
    (V : CekValue) (n : Nat) :
    runSteps sv s n = State.Halt V ↔ (runStepsWithCost sv s n).1 = State.Halt V := by
  rw [runStepsWithCost_fst]; exact runSteps_halt_iff_stepN sv s V n

@[simp] theorem runStepsWithCost_halt (sv : BuiltinSemanticsVariant) (V : CekValue) (n : Nat) :
    runStepsWithCost sv (State.Halt V) n = (State.Halt V, ExBudget.zero) := by
  cases n <;> simp [runStepsWithCost, runStepsCosting, builtinCallsCost]

@[simp] theorem runStepsWithCost_error (sv : BuiltinSemanticsVariant) (n : Nat) :
    runStepsWithCost sv State.Error n = (State.Error, ExBudget.zero) := by
  cases n <;> simp [runStepsWithCost, runStepsCosting, builtinCallsCost]

theorem runStepsCosting_add (sv : BuiltinSemanticsVariant) (s : State) (m n : Nat)
    (stepCost : ExBudget) (calls : List (BuiltinFun × List CekValue)) :
    runStepsCosting sv s (m + n) stepCost calls =
      runStepsCosting sv (runStepsCosting sv s m stepCost calls).1 n
        (runStepsCosting sv s m stepCost calls).2.1 (runStepsCosting sv s m stepCost calls).2.2 := by
  induction m generalizing s stepCost calls with
  | zero => cases s <;> simp [runStepsCosting]
  | succ m ih =>
      have heq : m + 1 + n = (m + n) + 1 := by omega
      rw [heq]
      cases s with
      | Halt V => cases n <;> simp [runStepsCosting]
      | Error => cases n <;> simp [runStepsCosting]
      | Eval st rho t => simp only [runStepsCosting]; exact ih _ _ _
      | Return st v => simp only [runStepsCosting]; exact ih _ _ _

/-- Costs add up along a run. -/
theorem runStepsWithCost_add (sv : BuiltinSemanticsVariant) (s : State) (m n : Nat) :
    runStepsWithCost sv s (m + n) =
      ((runStepsWithCost sv (runStepsWithCost sv s m).1 n).1,
       (runStepsWithCost sv s m).2 + (runStepsWithCost sv (runStepsWithCost sv s m).1 n).2) := by
  simp only [runStepsWithCost]
  rw [runStepsCosting_add, runStepsCosting_acc sv _ n]
  simp only [builtinCallsCost_append]
  congr 1
  -- `stepCost₁ + stepCost₂ + (calls₂ + calls₁) = stepCost₁ + calls₁ + (stepCost₂ + calls₂)`
  apply ExBudget.ext <;> simp only [ExBudget.add_cpu, ExBudget.add_mem] <;> omega

/-- No part of a run costs more than all of it. -/
theorem runStepsWithCost_cost_mono (sv : BuiltinSemanticsVariant) (s : State) (m n : Nat) :
    (runStepsWithCost sv s m).2 ≤ (runStepsWithCost sv s (m + n)).2 := by
  rw [runStepsWithCost_add]
  exact ExBudget.le_add_right _ _

/-- Once halted, more steps change neither the result nor its cost. -/
theorem runStepsWithCost_halt_stable (sv : BuiltinSemanticsVariant) (s : State) (V : CekValue)
    (cost : ExBudget) (m k : Nat) (h : runStepsWithCost sv s m = (State.Halt V, cost)) :
    runStepsWithCost sv s (m + k) = (State.Halt V, cost) := by
  rw [runStepsWithCost_add, h]
  simp

theorem ofCostedRun_success_iff (budget : ExBudget) (r : State × ExBudget) (V : CekValue)
    (consumed : ExBudget) :
    EvaluationResult.ofCostedRun budget r = EvaluationResult.Success V consumed ↔
      r = (State.Halt V, consumed) ∧ budget.canAfford consumed = true := by
  obtain ⟨σ, cost⟩ := r
  simp only [EvaluationResult.ofCostedRun]
  split
  · rename_i hc
    cases σ with
    | Halt V' =>
        simp only [EvaluationResult.Success.injEq, Prod.mk.injEq, State.Halt.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, hc⟩
        · rintro ⟨⟨rfl, rfl⟩, -⟩; exact ⟨rfl, rfl⟩
    | _ => simp
  · rename_i hc
    simp only [reduceCtorEq, false_iff, not_and, Prod.mk.injEq]
    rintro ⟨-, rfl⟩; exact hc

/-- A program that succeeds within its budget and step limit does the same with more of either,
    consuming the same. -/
theorem cekExecuteProgramWithBudget_success_stable (p : Program) (pv : PlutusVersion)
    (prv : ProtocolVersion) (params : List Term) (budget extra : ExBudget) (n k : Nat)
    (V : CekValue) (consumed : ExBudget)
    (h : cekExecuteProgramWithBudget p pv prv params budget n = EvaluationResult.Success V consumed) :
    cekExecuteProgramWithBudget p pv prv params (budget + extra) (n + k)
      = EvaluationResult.Success V consumed := by
  simp only [cekExecuteProgramWithBudget, ofCostedRun_success_iff] at h ⊢
  obtain ⟨hr, hc⟩ := h
  refine ⟨?_, ExBudget.canAfford_mono (ExBudget.le_add_right budget extra) hc⟩
  cases p with
  | Program ver body =>
      simp only [cekExecuteProgramWithCost, Prod.mk.injEq] at hr ⊢
      obtain ⟨h1, h2⟩ := hr
      have hs : runStepsWithCost (PlutusVersion.toSemanticsVariant pv prv)
          (initialState (applyParams body params)) n = (State.Halt V,
            (runStepsWithCost (PlutusVersion.toSemanticsVariant pv prv)
              (initialState (applyParams body params)) n).2) := by
        rw [← h1]
      rw [runStepsWithCost_halt_stable _ _ _ _ n k hs]
      exact ⟨rfl, h2⟩

end PlutusCore.UPLC.CekMachine
