import Blaster

import Cryptograph.BLS12_381.Basic
import PlutusCore.Crypto.BLS12_381

/-
  Does the Lean-blaster SMT translation accept BLS12-381 values at all?

  This is a tool-capability check, not a statement about the curve. Every goal below
  is trivially true (reflexivity, excluded middle, `True` in both branches); the only
  thing under test is whether `Translate` can build an SMT-LIB encoding of the *types*
  involved. Before `Fq1` was changed from `Fin fieldPrime` to a bare `Nat`
  (see `Cryptograph/BLS12_381/Basic.lean`), tests 1-6 all failed to elaborate with

      Inductive datatype with instance parameters not supported: Fin

  thrown by `genIndParams` (`Blaster/Smt/Translate/Quantifier.lean:959`), because `Fin`
  is parameterized by a *term* rather than a type universe. That error propagated up
  through `Fq2`/`Fq6`/`Fq12`, `Point Fq1` and `Option Fq12`, which is why no symbolic
  reasoning about this curve — or about any UPLC residual retaining a BLS value — was
  possible.

  Expected encodings, in increasing order of what they exercise:
    1. `Fq1`                    -> one parameterless datatype, a single `Nat` selector
    2. `Fq12`                   -> four nested datatypes, 12 `Int` leaves, and the
                                   `@isFq12 -> @isFq6 -> @isFq2 -> @isFq1 -> @isNat`
                                   well-formedness predicate chain
    3. `Point Fq1`              -> a one-type-parameter inductive with a nullary ctor
    4. `Option Fq12`            -> ditto, over the deep tower
    5. an `opaque` BLS builtin  -> `declare-fun` plus a codomain constraint
    6. `match` on an `opaque`   -> `ite` over constructor testers/selectors; the
       `Except`-returning builtin  residual the CEK machine actually leaves behind

  Note what test 6 does NOT show: the solver only learns that `uncompress` returns
  *some* `Except`, never that it returns `.ok`. Goals that need the success branch must
  supply that as a hypothesis.
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.BlasterSmoke

-- `Internal` rather than `Cryptograph.BLS12_381`: the latter re-`export`s the *type*
-- `Point`, but constructor dot-notation then resolves against the alias and misses
-- `Internal.Point.infinity`. `Cryptograph/BLS12_381/TestVectors.lean` opens it the same way.
open Cryptograph.BLS12_381.Internal
open PlutusCore.ByteString
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.Pairing

/- 1. A parameterless single-field structure over `Nat`. -/
#blaster [∀ (x y : Fq1), x = y → y = x]

/- 2. The full tower: a structure nesting 12 `Nat`s through three levels. -/
#blaster [∀ (x y : Fq12), x == y → y == x]

/- 3. A one-type-parameter inductive with a nullary constructor, over `Fq1`. -/
#blaster [∀ (p : Point Fq1), p = Point.infinity ∨ p ≠ Point.infinity]

/- 4. `Option` over the deep tower -- the Miller-loop result type. -/
#blaster [∀ (r : BLS12_381_MlResult), r.isNone = true ∨ r.isSome = true]

/- 5. An `opaque` builtin over G1: an uninterpreted function whose domain and
      codomain are both translatable datatypes. Congruence is all this gives. -/
#blaster [∀ (p q : BLS12_381_G1_Element), bls12_381_G1_add p q = bls12_381_G1_add p q]

/- 6. The shape a `#prep_uplc` residual actually stalls on: a `match` over an
      `opaque`, `Except`-returning builtin. `opaque` has no body the optimizer can
      unfold -- not even on concrete bytes -- so this term survives to the solver.

      The branches must *differ*: with `True` on both sides the optimizer collapses the
      match before translation and the test passes without encoding anything, which is
      how this file previously certified a capability Blaster did not have (see the
      **BLASTER** ledger entry in `ReclaimGlobalV2Properties.lean`). `Falsified` is the
      correct verdict here and is the point of the test: `uncompress` is uninterpreted,
      so the solver may answer `.error`, and a goal needing the success branch has to
      supply that as a premise. -/
#blaster (solve-result: 1) [∀ (b : ByteString),
  match bls12_381_G1_uncompress b with
  | .ok    _ => True
  | .error _ => False]

end PlutusCore.Crypto.BLS12_381.Tests.BlasterSmoke
