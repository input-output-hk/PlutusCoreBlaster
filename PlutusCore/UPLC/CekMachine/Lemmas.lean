import PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Term (Program Term)

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

end PlutusCore.UPLC.CekMachine
