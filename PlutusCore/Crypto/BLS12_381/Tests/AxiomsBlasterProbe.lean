import Blaster

import Cryptograph.BLS12_381.Basic
import PlutusCore.Crypto.BLS12_381

/-!
  # Can `blaster` use the axioms of `Crypto/BLS12_381/Axioms.lean`?

  A tool-capability check: nothing here is a statement about the curve. Three questions, in
  order -- whether the BLS *types* encode into SMT-LIB at all, whether the *axioms* about
  them reach the solver, and what the consumer has to do for the two group bundles.

  An axiom reaches the solver as a *premise of the goal*, which is the form every probe
  below uses: `#blaster [Axioms.SomeAlg → goal]`. Two things that do not work, for the
  record. An imported axiom is invisible -- only a same-module `axiom` is picked up, and
  then it is prepended to *every* query in that module, so this file declares none. And an
  imported axiom cannot be laundered in by restating it as a local theorem, however trivial
  the proof: a local theorem is skipped too.

  `(solve-result: 1)` pins an expected `Falsified`, `(solve-result: 2)` an expected
  `Undetermined`, and a bare `#guard_msgs in #blaster` an expected hard error -- so a
  capability regression fails the build rather than passing quietly.
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe

open Cryptograph.BLS12_381 (Fq1 Fq12 Point)

open PlutusCore.ByteString
open PlutusCore.Crypto.BLS12_381
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.G1.Internal (bls12_381_G1_add bls12_381_G1_uncompress)
open PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Crypto.BLS12_381.Pairing

/-! ## The types encode

    Every goal in this section is trivially true; the only thing under test is whether the
    translation can build an SMT-LIB encoding of the *types*, in increasing order of what
    they exercise. -/

/- `Fq1` -- one parameterless datatype, a single `Nat` selector. -/
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
   concrete bytes -- so the term survives to the solver.

   The branches must *differ*. With `True` on both sides the optimizer collapses the match
   before translation and the goal passes without encoding anything, which certifies nothing;
   that trap is worth knowing about, because a collapsed goal is indistinguishable from a
   solved one in the output. `Falsified` is the correct verdict: `uncompress` is
   uninterpreted, so the solver may answer `.error`, and a goal needing the success branch
   has to supply that as a premise. -/
#blaster (solve-result: 1) [∀ (b : ByteString),
  match bls12_381_G1_uncompress b with
  | .ok    _ => True
  | .error _ => False]

/-! ## Without the axioms, nothing is known

    `mulMlResult_comm` and `mulMlResult_assoc` are imported and make the goal true; the
    solver never sees them. `Falsified` with a concrete counterexample rather than
    `Undetermined`, because `mulMlResult` arrives as an ordinary uninterpreted function and
    Z3 is free to pick a non-commutative one. -/

#blaster (solve-result: 1) [∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x]

#blaster (solve-result: 1) [∀ (p q : BLS12_381_G1_Element),
  bls12_381_G1_add p q = bls12_381_G1_add q p]

/-! ## The `MlResult` layer

    A genuine two-step derivation -- commutativity twice and associativity once -- so a
    `Valid` here is use rather than restatement. -/

#blaster [Axioms.MlAlg → ∀ (x y z : BLS12_381_MlResult), (x * y) * z = (z * y) * x]

/-! `MlOk` is `axiom MlOk : BLS12_381_MlResult → Prop`. Its type is not a `Prop`, so it is
    never harvested even in its own module; it translates as an uninterpreted predicate,
    which is all this needs. -/

#blaster [Axioms.MlOkAlg → ∀ (x y : BLS12_381_MlResult),
  Axioms.MlOk (x * y) → Axioms.MlOk x]

#blaster [Axioms.BridgeAlg → ∀ (x y : BLS12_381_MlResult),
  bls12_381_finalVerify x y = true → Axioms.MlOk x]

/-! ## The ℤ/r layer needs no premise

    `GT` is a one-field structure and its operations are `def`s, so these four are `Valid`
    from the definitions alone -- there is no `gt*` axiom left to supply.

    Note the shape of the first goal. `∀ (x : Axioms.GT), x = x` would report `Valid`
    whether or not `GT` translates, because the optimizer discharges it beforehand and
    encodes nothing; a goal over `gtMul` cannot be collapsed that way. `Valid` rather than
    `Falsified` is itself the content: under the ℤ/r model `gtMul` really is commutative. -/

#blaster [∀ (x y : Axioms.GT), x * y = y * x]
#blaster [∀ (m n : Int), Axioms.gtGen ^ m = Axioms.gtGen ^ n ↔ m % Axioms.r = n % Axioms.r]
#blaster [∀ (m : Int), Axioms.gtGen ^ m = Axioms.gtGen ^ (m % Axioms.r)]
#blaster [∀ (m n : Int), Axioms.gtGen ^ (m + n) = Axioms.gtGen ^ m * Axioms.gtGen ^ n]

/-! ## The pairing bridge

    Two steps: `finalVerify_sound`, then `pi_millerLoop` on each side. This is
    `finalVerify_millerLoop_pair_sound` of `Axioms.lean`, reached from the two-conjunct
    slice rather than the whole bridge. -/

#blaster [Axioms.PairingBridgeAlg →
  ∀ (p₁ p₂ : BLS12_381_G1_Element) (q₁ q₂ : BLS12_381_G2_Element),
    bls12_381_finalVerify (bls12_381_millerLoop p₁ q₁) (bls12_381_millerLoop p₂ q₂) = true →
    Axioms.e p₁ q₁ = Axioms.e p₂ q₂]

/-! ## The pairing on the subgroup

    `e_dlog` twice over, with the ℤ/r layer closing the gap: equal `g2_dlog`s make the two
    exponents equal, and `gtPow` is a `def`, so the solver finishes without any `gt*`
    premise. The `InG1`/`InG2` guards are no obstacle -- they are `opaque`, hence
    uninterpreted predicates. -/

#blaster [Axioms.PairingAlg → ∀ (p : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
  Axioms.InG1 p → Axioms.InG2 q → Axioms.InG2 q' →
  Axioms.g2_dlog q = Axioms.g2_dlog q' → Axioms.e p q = Axioms.e p q']

/-! `millerLoop_ok` -- the third `PairingAlg` conjunct -- composed with `MlOkAlg`. -/

#blaster [Axioms.PairingAlg → Axioms.MlOkAlg →
  ∀ (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    Axioms.MlOk (bls12_381_millerLoop p q * bls12_381_millerLoop p q)]

/-! ## Serialisation, and the subgroup seam

    Two steps: `g1_uncompress_subgroup` for the guard, then `g1_uncompress_compress` under
    it. The conclusion is over `Axioms.InG1` itself rather than a stand-in predicate, which
    is what makes this a fact about the real subgroup. `SerdeAlg` rather than
    `PairingSerdeAlg`, to keep the premise to what the goal uses. -/

#blaster [Axioms.SerdeAlg → ∀ (b : ByteString) (p : BLS12_381_G1_Element),
  bls12_381_G1_uncompress b = Except.ok p →
  Axioms.InG1 p ∧ bls12_381_G1_uncompress (bls12_381_G1_compress p) = Except.ok p]

/-! ## `DlogFacts` -- derived facts, passed because the solver cannot re-derive them

    `Axioms.DlogFacts` is not axioms: every conjunct is a theorem of `Axioms.lean`. It is
    bundled as a premise all the same, because `g1_dlog` is uninterpreted and the `∃` that
    would tie it to the generator is behind `InG1_def`, so no query can reconstruct any of
    it.

    Two steps, and a statement worth having: equal dlog products make the *on-chain* check
    pass. `e_eq_iff_dlog` turns the arithmetic premise into a pairing equality, and
    `finalVerify_millerLoop_pair` turns that into `finalVerify ... = true`. -/

set_option warn.sorry false in
theorem probe_dlog_finalVerify_of (h : Axioms.DlogFacts) :
  ∀ (p p' : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    Axioms.InG1 p' → p' ≠ 0 → Axioms.InG2 q' → q' ≠ 0 →
    (Axioms.g1_dlog p * Axioms.g2_dlog q) % Axioms.r
      = (Axioms.g1_dlog p' * Axioms.g2_dlog q') % Axioms.r →
    bls12_381_finalVerify (bls12_381_millerLoop p q) (bls12_381_millerLoop p' q') = true := by
      blaster

theorem probe_dlog_finalVerify :
  ∀ (p p' : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
    Axioms.InG1 p → p ≠ 0 → Axioms.InG2 q → q ≠ 0 →
    Axioms.InG1 p' → p' ≠ 0 → Axioms.InG2 q' → q' ≠ 0 →
    (Axioms.g1_dlog p * Axioms.g2_dlog q) % Axioms.r
      = (Axioms.g1_dlog p' * Axioms.g2_dlog q') % Axioms.r →
    bls12_381_finalVerify (bls12_381_millerLoop p q) (bls12_381_millerLoop p' q') = true :=
  probe_dlog_finalVerify_of Axioms.dlogFacts

/-! This is the one probe written as a theorem rather than a `#blaster` command, because the
    footprint is the point and only a real proof term has one. No *new* axiom appears --
    `DlogFacts` is theorems -- but the proofs behind those theorems run through `g1_cyclic`,
    so the G1/G2 scalar-action axioms and `InG1_def` are named here even though the goal
    mentions no point operation at all. "Free" means free of new assumptions, not free in
    the audit. -/

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe.probe_dlog_finalVerify' depends on axioms: [propext,
 Quot.sound,
 Blaster.Tactic.blasterProven,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.InG1_def,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.InG2_def,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.MlOk,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.e,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.e_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.finalVerify_complete,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.finalVerify_sound,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_dlog_scalarMul,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_mod,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_one,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_zero,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_dlog_scalarMul,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_mod,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_one,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_zero,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.millerLoop_ok,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi_millerLoop]
-/
#guard_msgs in
#print axioms probe_dlog_finalVerify

/-! `g1_dlog_emod_eq_zero_iff` twice over: two subgroup points whose dlogs vanish mod r are
    the same point, both being zero. The kind of step `acceptedPubUnique` takes by hand in
    `Tests/OwnershipVerifyExample.lean`. -/

#blaster [Axioms.DlogFacts → ∀ (p p' : BLS12_381_G1_Element),
  Axioms.InG1 p → Axioms.InG1 p' →
  Axioms.g1_dlog p % Axioms.r = 0 → Axioms.g1_dlog p' % Axioms.r = 0 → p = p']

/-! ## The remaining wall: G1/G2 arithmetic is a `partial def`

    `G1Alg` and `G2Alg` state their conclusions as equations in the `Cryptograph` `+`/`*`,
    computable operations that bottom out in the `partial def` `binaryInversion.loop`. The
    translation refuses those outright -- a hard error, not an `Undetermined`. -/

/--
error: normConst: partial function not supported Cryptograph.BLS12_381.Internal.binaryInversion.loop !!!
-/
#guard_msgs in
#blaster [∀ (p q : BLS12_381_G1_Element), p + q = q + p]

/-! ### Where the seal's reach stops

    Sealing a plain `def` does nothing -- the translation reaches a `def`'s body directly, so
    the wall is exactly where it was. It is instance *resolution* the attribute blocks, which
    is why the seal below names the four `Point` instances and not `pointAdd`/`pointMul`. An
    `opaque` wrapper is the tool for a wall behind a plain function instead; that is how the
    BLS builtins translate at all. -/

def plainAdd (p q : BLS12_381_G1_Element) : BLS12_381_G1_Element := p + q

attribute [local irreducible] plainAdd

/--
error: normConst: partial function not supported Cryptograph.BLS12_381.Internal.binaryInversion.loop !!!
-/
#guard_msgs in
#blaster [∀ (p q : BLS12_381_G1_Element), plainAdd p q = plainAdd q p]

/-- The same wrapper as an `opaque`, which the translation does keep uninterpreted. -/
opaque opaqueAdd (p q : BLS12_381_G1_Element) : BLS12_381_G1_Element := p + q

#blaster (solve-result: 1) [∀ (p q : BLS12_381_G1_Element), opaqueAdd p q = opaqueAdd q p]

/-! ## Past the wall: the seal

    Make the `Cryptograph` point operations uninterpreted for the rest of this module.
    `local`, so it cannot escape. The four instances are field-polymorphic, so the one seal
    covers `Point Fq1` and `Point Fq2` alike.

    **This section is last on purpose.** The attribute takes effect at its position and
    changes every `blaster` call after it, so nothing that measures the unsealed behaviour
    can follow it. Sealing costs nothing in the trust base -- an attribute is not a proof
    step, as the footprint below shows. -/

macro "seal_bls_point_ops" : command =>
  `(attribute [local irreducible]
      Cryptograph.BLS12_381.Internal.instAddPointOfDecidableEqOfField
      Cryptograph.BLS12_381.Internal.instNegPointOfField
      Cryptograph.BLS12_381.Internal.instHMulIntPointOfDecidableEqOfField
      Cryptograph.BLS12_381.Internal.instHMulNatPointOfDecidableEqOfField)

seal_bls_point_ops

/-! The identical goal now reaches the solver. `Falsified` rather than `Valid` is the point:
    commutativity is not true of an arbitrary uninterpreted function, so Z3 builds a
    counterexample, which is proof that the goal was genuinely translated rather than
    discharged by the optimizer. -/

#blaster (solve-result: 1) [∀ (p q : BLS12_381_G1_Element), p + q = q + p]

/-! ### G1 and G2 group laws as a premise

    `G1AddNegAlg`, the additive slice of `G1Alg`: `g1_add_comm` to turn `0 + _` around,
    `g1_add_zero` twice, `g1_add_neg` once. -/

set_option warn.sorry false in
theorem sealed_group_of (h : Axioms.G1AddNegAlg) :
  ∀ (p : BLS12_381_G1_Element), Axioms.InG1 p → (0 + (p + -p)) + 0 = 0 := by blaster

/-- Discharged from the real axioms, so the footprint names them and nothing else. -/
theorem sealed_group :
  ∀ (p : BLS12_381_G1_Element), Axioms.InG1 p → (0 + (p + -p)) + 0 = 0 :=
  sealed_group_of Axioms.g1AddNegAlg

/-! The footprint is the three real axioms and nothing more. Two things it does *not*
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

/-! ### The scalar action, including the huge modulus

    `g1_scalarMul_mod` compares against `r`, a 255-bit constant, which was the suspected
    reason the full bundle stalls. It is not: `G1SmulAlg` carries it and leaves the goal
    `Valid`. -/

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

#blaster (timeout: 30) (solve-result: 2) [Axioms.G1Alg →
  ∀ (p q : BLS12_381_G1_Element), p + q = p]

end PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterProbe
