import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.Utils

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

namespace PlutusCore.UPLC.CekMachine

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
          | Error      => simp [runSteps] at h
          | Eval _ _ _ => rfl
          | Return _ _ => rfl
      | succ n ih =>
          intro m s v h
          cases s with
          | Halt w     => rfl
          | Error      => simp [runSteps] at h
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
