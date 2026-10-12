import PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Term (Program Term BuiltinFun)
open PlutusCore.UPLC.ExBudget (ExBudget)

/-! ## Step iteration with no exhaustion branch

`stepN` takes a step count and recurses on it exactly as `runSteps` does. What it lacks is
the exhaustion branch: at zero it hands back the state reached where `runSteps` reports
`Error`, so a run splits into two analyzable pieces. -/

/-- `step`, but a no-op on `Halt`/`Error`, which raw `step` sends to `Error`. -/
def stepAbs (sv : BuiltinSemanticsVariant) (s : State) : State :=
  match s with
  | State.Halt V => State.Halt V
  | State.Error => State.Error
  | _ => step sv s

/-- Iteration of `stepAbs`. -/
def stepN (sv : BuiltinSemanticsVariant) (s : State) : Nat → State
  | 0 => s
  | (k + 1) => stepN sv (stepAbs sv s) k

@[simp] theorem runSteps_halt (sv : BuiltinSemanticsVariant) (V : CekValue) (n : Nat) :
    runSteps sv (State.Halt V) n = State.Halt V := by
  cases n <;> rfl

@[simp] theorem runSteps_error (sv : BuiltinSemanticsVariant) (n : Nat) :
    runSteps sv State.Error n = State.Error := by
  cases n <;> rfl

/-- `stepAbs` agrees with `step` off `Halt`/`Error`, and is a no-op on them. -/
theorem stepAbs_not_halt_error (sv : BuiltinSemanticsVariant) (s : State)
    (h1 : ∀ V, s ≠ State.Halt V) (h2 : s ≠ State.Error) :
    stepAbs sv s = step sv s := by
  unfold stepAbs
  cases s with
  | Halt V => exact absurd rfl (h1 V)
  | Error => exact absurd rfl h2
  | Eval _ _ _ => rfl
  | Return _ _ => rfl

/-- One step of `runSteps` folds into one of `stepAbs`, with no hypothesis on `s`. -/
theorem runSteps_succ (sv : BuiltinSemanticsVariant) (s : State) (k : Nat) :
    runSteps sv s (k + 1) = runSteps sv (stepAbs sv s) k := by
  cases s with
  | Halt V => simp [stepAbs]
  | Error => simp [stepAbs]
  | Eval st rho t => rfl
  | Return st v => rfl

/-- Once halted at `m` steps, still halted at `m + k` steps for any extra fuel `k`. -/
theorem runSteps_halt_stable (sv : BuiltinSemanticsVariant) (s : State) (V : CekValue)
    (m k : Nat) (h : runSteps sv s m = State.Halt V) :
    runSteps sv s (m + k) = State.Halt V := by
  induction m generalizing s with
  | zero =>
      cases s with
      | Halt V' =>
          simp only [runSteps] at h
          cases h
          simp [runSteps_halt]
      | Error =>
          simp only [runSteps] at h
          injection h
      | Eval st rho t =>
          simp only [runSteps] at h
          injection h
      | Return st v =>
          simp only [runSteps] at h
          injection h
  | succ n ih =>
      rw [runSteps_succ] at h
      have : runSteps sv s (n + 1 + k) = runSteps sv (stepAbs sv s) (n + k) := by
        have heq : n + 1 + k = (n + k) + 1 := by omega
        rw [heq, runSteps_succ]
      rw [this]
      exact ih (stepAbs sv s) h

/-- Fuel composition, with no side condition. Two properties of `stepAbs` carry it:
    absorption, which is what makes `runSteps_succ` hold on the terminal states, and the
    absence of a fuel-exhaustion branch, which is why the prefix yields the state reached
    where `runSteps sv (runSteps sv s m) n` yields `Error`. -/
theorem runSteps_add (sv : BuiltinSemanticsVariant) (s : State) (m n : Nat) :
    runSteps sv s (m + n) = runSteps sv (stepN sv s m) n := by
  induction m generalizing s with
  | zero => simp [stepN]
  | succ k ih =>
      have heq : k + 1 + n = (k + n) + 1 := by omega
      rw [heq, runSteps_succ, ih (stepAbs sv s)]
      rfl

/-- `runSteps` and `stepN` agree exactly on halting runs. -/
theorem runSteps_halt_iff_stepN (sv : BuiltinSemanticsVariant) (s : State) (V : CekValue)
    (m : Nat) :
    runSteps sv s m = State.Halt V ↔ stepN sv s m = State.Halt V := by
  have key : runSteps sv s m = runSteps sv (stepN sv s m) 0 := by
    simpa using runSteps_add sv s m 0
  rw [key]
  cases hst : stepN sv s m with
  | Halt V' => simp [runSteps]
  | Error => simp [runSteps]
  | Eval st rho t => simp [runSteps]
  | Return st v => simp [runSteps]

/-- A program's result does not depend on how much fuel it was given, past enough. -/
theorem cekExecuteProgramWithSemanticVariant_halt_stable
    (sv : BuiltinSemanticsVariant) (p : Program) (params : List Term) (V : CekValue) (n k : Nat)
    (h : cekExecuteProgramWithSemanticVariant sv p params n = State.Halt V) :
    cekExecuteProgramWithSemanticVariant sv p params (n + k) = State.Halt V := by
  cases p with
  | Program ver body =>
      simp only [cekExecuteProgramWithSemanticVariant] at h ⊢
      exact runSteps_halt_stable sv _ V n k h

/-- The same, at the default semantics variant. -/
theorem cekExecuteProgram_halt_stable
    (p : Program) (params : List Term) (V : CekValue) (n k : Nat)
    (h : cekExecuteProgram p params n = State.Halt V) :
    cekExecuteProgram p params (n + k) = State.Halt V :=
  cekExecuteProgramWithSemanticVariant_halt_stable default p params V n k h

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

/-! ## Costs

`runStepsWithCost` takes the steps `runSteps` takes, stopping where `stepN` does, and adds up what
they cost. Costs add up along a run, so no part of a run costs more than all of it, which is what
lets `EvaluationResult.ofCostedRun` judge a run by its total. -/

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
