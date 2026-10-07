import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.Utils

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Term (Program Term)

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
