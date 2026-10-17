import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.Utils

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

/-!
  ## Fuel-honest error observation for the CEK machine

  `runSteps` returns `State.Error` both for a genuine machine error and for step-limit
  exhaustion (`CekMachine.lean`, the `| 0, _ => State.Error` case). `Utils.isUnsuccessful`
  inherits that conflation, so on its own no finite-fuel run can distinguish "the program
  rejected" from "I ran out of steps" — and therefore cannot support a rejection claim.

  `erroredWithin` separates the two: it reports `false` when it merely runs out. The two
  lemmas below then lift a single bounded observation to a statement about *every* fuel,
  which is what makes properties phrased with it fuel-monotone rather than bounded-model
  artifacts.

  These live here rather than in `Utils` because they step the machine, whereas the
  predicates in `Utils` classify a `State` that is already in hand.
-/

open PlutusCore.UPLC.Term (Term Program)
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Utils (isSuccessful isHaltState)

/-- `true` iff the machine reaches `State.Error` within `n` steps, starting from `s`.
    Running out of steps yields `false`, not `true` — the difference from `runSteps`. -/
def erroredWithin (n : Nat) (s : State) : Bool :=
  match n, s with
  | _, .Halt _ => false
  | _, .Error  => true
  | 0, _       => false
  | n+1, s     => erroredWithin n (step default s)

/-- `erroredWithin` for a whole program applied to `args`, saving callers the destructuring
    of `Program`. This is the form `cekExecuteProgram` results are compared against. -/
def erroredWithinProgram (n : Nat) (p : Program) (args : List Term) : Bool :=
  match p with
  | .Program _ body => erroredWithin n (initialState (applyParams body args))

/-- If the machine halts at any fuel then it never errored, at any prefix length.

    This is the load-bearing lemma: it is what lets a property proved at one fuel be read
    as a property of every fuel. -/
theorem not_erroredWithin_of_halt (n : Nat) : ∀ (m : Nat) (s : State) (v : CekValue),
  runSteps default s m = .Halt v
  ------------------------------
  → erroredWithin n s = false :=
    by
      induction n with
      | zero =>
          intro m s v h
          cases s with
          | Halt w     => rfl
          | Error      => simp at h
          | Eval _ _ _ => rfl
          | Return _ _ => rfl
      | succ n ih =>
          intro m s v h
          cases s with
          | Halt w     => rfl
          | Error      => simp at h
          | Eval a b c =>
              cases m with
              | zero    => simp [runSteps] at h
              | succ m' => exact ih m' _ v (by simpa [runSteps] using h)
          | Return a b =>
              cases m with
              | zero    => simp [runSteps] at h
              | succ m' => exact ih m' _ v (by simpa [runSteps] using h)

/-- The contrapositive, at program level: a successful execution at *any* fuel `m` forces
    every `erroredWithin` observation on the same program and arguments to be `false`. -/
theorem not_erroredWithinProgram_of_isSuccessful (n m : Nat) (p : Program) (args : List Term) :
  isSuccessful (cekExecuteProgram p args m)
  -----------------------------------------
  → erroredWithinProgram n p args = false :=
    by
      intro h
      cases p with
      | Program ver body =>
          simp only [cekExecuteProgram, cekExecuteProgramWithSemanticVariant] at h
          simp only [erroredWithinProgram]
          cases hres : runSteps default (initialState (applyParams body args)) m with
          | Halt v     => exact not_erroredWithin_of_halt n m _ v hres
          | Error      => rw [hres] at h; exact absurd h (by simp [isSuccessful, isHaltState])
          | Eval _ _ _ => rw [hres] at h; exact absurd h (by simp [isSuccessful, isHaltState])
          | Return _ _ => rw [hres] at h; exact absurd h (by simp [isSuccessful, isHaltState])

/-- A program that errors within `n` steps on `args` is not successful at any fuel. The
    form to reach for when starting from a concrete rejection rather than an implication. -/
theorem not_isSuccessful_of_erroredWithinProgram (n m : Nat) (p : Program) (args : List Term) :
  erroredWithinProgram n p args = true
  ------------------------------------
  → ¬ isSuccessful (cekExecuteProgram p args m) :=
      by
        intros herr hacc
        rw [not_erroredWithinProgram_of_isSuccessful n m p args hacc] at herr
        exact Bool.noConfusion herr

end PlutusCore.UPLC.CekMachine
