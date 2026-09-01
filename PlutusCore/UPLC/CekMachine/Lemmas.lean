import PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Term (Program Term)

/-! ## Fuel-free step iteration

`stepAbs`/`stepN` iterate `step` without fuel, returning the state reached instead of
`runSteps`'s fuel-exhaustion `Error`, so a run splits into two analyzable pieces. -/

/-- `step`, but a no-op on `Halt`/`Error`, which raw `step` sends to `Error`. -/
def stepAbs (sv : BuiltinSemanticsVariant) (s : State) : State :=
  match s with
  | State.Halt V => State.Halt V
  | State.Error => State.Error
  | _ => step sv s

/-- Fuel-free iteration of `stepAbs`. -/
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

/-- The fuelled machine and the fuel-free iteration agree exactly on halting runs. -/
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

end PlutusCore.UPLC.CekMachine
