import Blaster

import Cryptograph.BLS12_381.Basic
import PlutusCore.Crypto.BLS12_381

/-!
  # Can `blaster` use the axioms of `Crypto/BLS12_381/Axioms.lean`?
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe

open Cryptograph.BLS12_381 (Fq1 Fq12 Point)

open PlutusCore.ByteString
open PlutusCore.Crypto.BLS12_381
open PlutusCore.Crypto.BLS12_381.Axioms (e gtGen MlOk r)
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.G1 (bls12_381_G1_add bls12_381_G1_uncompress)
open PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Crypto.BLS12_381.Pairing

set_option warn.sorry false

/-! ## The types encode -/

/- `Fq1` -/
#blaster [∀ (x y : Fq1), x = y → y = x]

/- `Fq12` -- four nested datatypes, 12 `Int` leaves, and the
   `@isFq12 → @isFq6 → @isFq2 → @isFq1 → @isNat` well-formedness predicate chain. -/
#blaster [∀ (x y : Fq12), x == y → y == x]

/- `Point Fq1` -- a one-type-parameter inductive with a nullary constructor. -/
#blaster [∀ (p : Point Fq1), p = Point.infinity ∨ p ≠ Point.infinity]

/- `Option Fq12`, the Miller-loop result type -- the same, over the deep tower. -/
#blaster [∀ (r : BLS12_381_MlResult), r.isNone = true ∨ r.isSome = true]

/- An `opaque` builtin over G1: an uninterpreted function whose domain and codomain are both
   translatable datatypes. Congruence is all this gives. -/
#blaster [∀ (p q : BLS12_381_G1_Element), bls12_381_G1_add p q = bls12_381_G1_add p q]

/- The shape a `#prep_uplc` residual stalls on: a `match` over an `opaque`,
   `Except`-returning builtin, which has no body the optimizer can unfold -- not even on
   concrete bytes -- so the term survives to the solver. -/
#blaster (solve-result: 1) (gen-cex: 0) [∀ (b : ByteString),
  match bls12_381_G1_uncompress b with
  | .ok    _ => True
  | .error _ => False]

/-! ## Without the axioms, nothing is known -/

#blaster (solve-result: 1) (gen-cex: 0) [∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x]

#blaster (solve-result: 1) (gen-cex: 0) [∀ (p q : BLS12_381_G1_Element), bls12_381_G1_add p q = bls12_381_G1_add q p]

/-! ## The `MlResult` layer -/

#blaster [Axioms.MlAlg → ∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x]

/-! `MlOk` is `axiom MlOk : BLS12_381_MlResult → Prop`. -/

#blaster [Axioms.MlOkAlg → ∀ (x y : BLS12_381_MlResult), MlOk (x * y) → MlOk x]

#blaster [Axioms.BridgeAlg → ∀ (x y : BLS12_381_MlResult), bls12_381_finalVerify x y = true → MlOk x]

/-! ## The ℤ/r layer needs no premise -/

#blaster [∀ (x y : Axioms.GT), x * y = y * x]
#blaster [∀ (m n : Int), gtGen ^ m = gtGen ^ n ↔ m % r = n % r]
#blaster [∀ (m : Int), gtGen ^ m = gtGen ^ (m % r)]
#blaster [∀ (m n : Int), gtGen ^ (m + n) = gtGen ^ m * gtGen ^ n]

/-! ## The pairing bridge -/

#blaster [Axioms.PairingBridgeAlg →
  ∀ (p₁ p₂ : BLS12_381_G1_Element) (q₁ q₂ : BLS12_381_G2_Element),
    bls12_381_finalVerify (bls12_381_millerLoop p₁ q₁) (bls12_381_millerLoop p₂ q₂) = true →
    e p₁ q₁ = e p₂ q₂]

/-! ## The pairing on the subgroup  -/

#blaster [Axioms.PairingAlg → ∀ (p : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
  Axioms.InG1 p → Axioms.InG2 q → Axioms.InG2 q' →
  Axioms.g2_dlog q = Axioms.g2_dlog q' → e p q = e p q']

/-! `millerLoop_ok` -- the third `PairingAlg` conjunct -- composed with `MlOkAlg`. -/

#blaster [Axioms.PairingAlg → Axioms.MlOkAlg →
  ∀ (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    MlOk (bls12_381_millerLoop p q * bls12_381_millerLoop p q)]

/-! ## Serialisation, and the subgroup seam -/

#blaster [Axioms.SerdeAlg → ∀ (b : ByteString) (p : BLS12_381_G1_Element),
  bls12_381_G1_uncompress b = Except.ok p →
  Axioms.InG1 p ∧ bls12_381_G1_uncompress (bls12_381_G1_compress p) = Except.ok p]

/-! ## `DlogFacts` -- derived facts, passed because the solver cannot re-derive them -/

theorem probe_dlog_finalVerify_of (h : Axioms.DlogFacts) :
  ∀ (p p' : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    Axioms.InG1 p' → p' ≠ 0 → Axioms.InG2 q' → q' ≠ 0 →
    (Axioms.g1_dlog p * Axioms.g2_dlog q) % r = (Axioms.g1_dlog p' * Axioms.g2_dlog q') % r →
    ------------------------------------------------------------------------------------------
    bls12_381_finalVerify (bls12_381_millerLoop p q) (bls12_381_millerLoop p' q') = true :=
      by blaster

theorem probe_dlog_finalVerify :
  ∀ (p p' : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    Axioms.InG1 p' → p' ≠ 0 → Axioms.InG2 q' → q' ≠ 0 →
    (Axioms.g1_dlog p * Axioms.g2_dlog q) % r = (Axioms.g1_dlog p' * Axioms.g2_dlog q') % r →
    ------------------------------------------------------------------------------------------
    bls12_381_finalVerify (bls12_381_millerLoop p q) (bls12_381_millerLoop p' q') = true :=
      have h := probe_dlog_finalVerify_of Axioms.dlogFacts
      by blaster

/-! `g1_dlog_emod_eq_zero_iff` twice over: two subgroup points whose dlogs vanish mod r are
    the same point, both being zero. The kind of step `acceptedPubUnique` takes by hand in
    `Tests/OwnershipVerifyExample.lean`. -/

#blaster [Axioms.DlogFacts → ∀ (p p' : BLS12_381_G1_Element),
  Axioms.InG1 p → Axioms.InG1 p' →
  Axioms.g1_dlog p % r = 0 → Axioms.g1_dlog p' % r = 0 → p = p']

/-! The goal reaches the solver, and `AllAlg` carries `g1_add_comm`, so commutativity of the
    sealed `+` is `Valid` from the axiom rather than from the body of `pointAdd`. -/

#blaster [Axioms.AllAlg → ∀ (p q : BLS12_381_G1_Element), p + q = q + p]

/-! ### G1 and G2 group laws as a premise -/

#blaster (timeout: 30) (solve-result: 1) [∀ (p : BLS12_381_G1_Element),
  Axioms.InG1 p → (0 + (p + -p)) + 0 = 0]

theorem sealed_group_of (h : Axioms.G1AddNegAlg) :
  ∀ (p : BLS12_381_G1_Element), Axioms.InG1 p → (0 + (p + -p)) + 0 = 0 := by blaster

/-- Discharged from the real axioms, so the footprint names them and nothing else. -/
theorem sealed_group :
  ∀ (p : BLS12_381_G1_Element), Axioms.InG1 p → (0 + (p + -p)) + 0 = 0 :=
    by
      have h := sealed_group_of Axioms.g1AddNegAlg
      blaster

/-! The footprint is the axioms it really used and nothing else. Two things it does *not*
    contain: any artefact of the seal, and `InG1_def`, because nothing here unfolded the
    guard. That is what makes sealing preferable to restating the laws over the `opaque`
    builtins, which would need a definitional bridge axiom per operation. -/

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe.sealed_group' depends on axioms: [propext,
 Quot.sound,
 Blaster.Tactic.blasterProven,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_add_comm,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_add_neg,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_add_zero]
-/
#guard_msgs in
#print axioms sealed_group

/-! The same shape on G2, to show the one seal covers both groups. -/

#blaster [Axioms.G2AddNegAlg →
  ∀ (q : BLS12_381_G2_Element), Axioms.InG2 q → (0 + (q + -q)) + 0 = 0]

/-! ### The scalar action, including the huge modulus  -/

#blaster [Axioms.G1SmulAlg →
  ∀ (p q : BLS12_381_G1_Element), (1 : Int) * (p + q) = q + p]

/-! ### The limit, pinned as a limit

    The same goal from the whole twelve-conjunct `G1Alg` instead of the three laws it needs.
    `Undetermined`: the premise set is too large for the solver, not untranslatable. Pinned
    so that a future improvement shows up here as a failing expectation rather than going
    unnoticed. -/

#blaster (timeout: 30) (solve-result: 2) [Axioms.G1Alg →
  ∀ (p q : BLS12_381_G1_Element), Axioms.InG1 p → Axioms.InG1 q → (1 : Int) * (p + q) = q + p]

/-! ### The vacuity guards

    Both must stay `Undetermined`. A `Valid` here would mean the encoded premise set is
    contradictory and every sealed result above is worthless. -/

#blaster (timeout: 30) (solve-result: 2) [Axioms.G1AddNegAlg → False]

#blaster (timeout: 30) (solve-result: 2) [Axioms.G1Alg → ∀ (p q : BLS12_381_G1_Element), p + q = p]

end PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe
