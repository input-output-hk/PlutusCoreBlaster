import Blaster

import PlutusCore.Crypto.BLS12_381

/-!
  # Past the last wall: `G1Alg`/`G2Alg` by sealing the point operations

  `AxiomsBlasterProbe.lean` pins the wall this file gets past. The `Cryptograph` point
  operations are computable and bottom out in the `partial def` `binaryInversion.loop`, and
  `normConst` refuses partial functions
  (`Blaster/Optimize/Rewriting/OptimizeConst.lean:85-93`) -- so any premise or goal mentioning
  the point `+`/`*`/`-` was a hard error, which put `G1Alg` and `G2Alg` (24 of the 42 Prop
  axioms) out of reach at any phrasing.

  The gate is reached while blaster *unfolds a constant*. So it is enough to stop the descent
  before it arrives: mark the four `Cryptograph` `Point` instances `irreducible` and blaster
  keeps `Add.add inst x y` as an application it cannot look inside, which is exactly the
  uninterpreted function a group law wants. Measured with `(dump-smt-lib: 1)`, the sealed `+`
  becomes a single

      (declare-fun @Add.add._uniq.N ((Point Fq1) (Point Fq1)) (Point Fq1))

  over the real datatype sort, shared by premise and goal. The four instances are
  field-polymorphic (`instance {α} [Field α] : Add (Point α)`), so one seal covers G1 and G2
  both. Nothing in `Axioms.lean` or `Cryptograph` changes and no axiom is added -- this is the
  one route past a wall in this project that costs nothing at all.

  ## Why this is its own module

  `attribute [local irreducible]` applies from its position to the end of the file, so it
  changes the encoding of *every* later `blaster` call. That is the same module-wide reach
  that made `AxiomsBlasterHarvest.lean` a separate file, and it wants the same treatment: the
  probe's pinned results must keep measuring an unsealed world.

  ## Two things to keep in view

  **Vacuity.** Sealing hands the solver an uninterpreted function, so a premise set that is
  contradictory *in the encoding* would make every goal `Valid` for the wrong reason. The
  guards below are the standing check: `[premise → False]` and a goal that must not follow
  are both expected `Undetermined`, never `Valid`. If a Blaster bump ever turns one of them
  `Valid`, every sealed proof in the project is worthless and this file fails loudly.

  Note also that blaster's reliance on reducibility here is narrower than "blaster honours
  `irreducible`" — measured, it does not. `normConst` checks `isPartialDef` on the constant
  it is handed and never consults reducibility, and sealing a *plain `def`* that wraps the
  point `+` leaves the error exactly where it was (pinned below). What the seal actually
  blocks is **instance resolution**: `Add.add inst x y` can only become `pointAdd x y` by
  unfolding `inst`, and that step does respect the attribute. So the trick reaches walls
  behind a class instance and no others — the `BitVec` wall inside `sliceByteString`, for
  one, is untouched by it, and needs an `opaque` wrapper instead. That is a thin contract to
  rest on, which is the other reason these tests are pinned.

  **Premise size, not translatability, is the real limit.** Every individual law works.
  Passing all twelve conjuncts of `G1Alg` at once does not: the same goal that is `Valid`
  from a three-conjunct premise comes back `Undetermined` from the whole bundle. So state the
  two or three laws the goal needs, as `G1AddNegAlg` does below. This is the same advice the
  footprint argument gives for `BlasterAlg`, arrived at from the opposite direction.
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterSealed

open Cryptograph.BLS12_381
open PlutusCore.Crypto.BLS12_381
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Crypto.BLS12_381.Axioms

/-! ## Before and after, in one file

    The attribute takes effect at its position, so the same goal can be measured on both
    sides of it. First unsealed -- the wall, verbatim as the probe pins it. -/

/--
error: normConst: partial function not supported Cryptograph.BLS12_381.Internal.binaryInversion.loop !!!
-/
#guard_msgs in
#blaster [∀ (p q : BLS12_381_G1_Element), p + q = q + p]

/-! ### Where the seal's reach stops, measured before sealing anything

    Sealing a plain `def` does nothing: blaster reaches a `def`'s body directly, so the wall
    is exactly where it was. It is instance *resolution* that the attribute blocks, which is
    why the seal below names the four instances and not `pointAdd`/`pointMul`. An `opaque`
    wrapper is the tool for a wall that sits behind a plain function instead — that is how
    the BLS builtins translate, and it is the route obligation 8 of
    `ReclaimGlobalV2Bridge.lean` needs for `sliceByteString`. -/

def plainAdd (x y : BLS12_381_G1_Element) : BLS12_381_G1_Element := x + y

attribute [local irreducible] plainAdd

/--
error: normConst: partial function not supported Cryptograph.BLS12_381.Internal.binaryInversion.loop !!!
-/
#guard_msgs in
#blaster [∀ (p q : BLS12_381_G1_Element), plainAdd p q = plainAdd q p]

/-- The same wrapper as an `opaque`, which blaster does keep uninterpreted. -/
opaque opaqueAdd (x y : BLS12_381_G1_Element) : BLS12_381_G1_Element := x + y

#blaster (solve-result: 1) [∀ (p q : BLS12_381_G1_Element), opaqueAdd p q = opaqueAdd q p]

/-- Make the `Cryptograph` point operations uninterpreted to `blaster` for the rest of this
    file. `local`, so it cannot escape the module; the four instances are field-polymorphic,
    so this covers `Point Fq1` and `Point Fq2` alike. -/
macro "seal_bls_point_ops" : command =>
  `(attribute [local irreducible]
      Cryptograph.BLS12_381.Internal.instAddPointOfDecidableEqOfField
      Cryptograph.BLS12_381.Internal.instNegPointOfField
      Cryptograph.BLS12_381.Internal.instHMulIntPointOfDecidableEqOfField
      Cryptograph.BLS12_381.Internal.instHMulNatPointOfDecidableEqOfField)

seal_bls_point_ops

/-! And after: the identical goal now reaches the solver. `Falsified` rather than `Valid` is
    the point -- commutativity is not true of an arbitrary uninterpreted function, so Z3
    builds a counterexample, which is proof that the goal was genuinely translated rather
    than discharged by the optimizer. -/

#blaster (solve-result: 1) [∀ (p q : BLS12_381_G1_Element), p + q = q + p]

/-! ## The capability: G1 group laws as a premise

    Three of `G1Alg`'s conjuncts, and a goal needing all three: `g1_add_comm` to turn
    `0 + _` around, `g1_add_zero` twice, `g1_add_neg` once. -/

/-- The additive part of `G1Alg`, at the size the solver actually handles. -/
def G1AddNegAlg : Prop :=
  (∀ (x y : BLS12_381_G1_Element), x + y = y + x) ∧
  (∀ (x : BLS12_381_G1_Element), x + 0 = x) ∧
  (∀ (x : BLS12_381_G1_Element), InG1 x → x + -x = 0)

theorem g1AddNegAlg : G1AddNegAlg := ⟨g1_add_comm, g1_add_zero, g1_add_neg⟩

set_option warn.sorry false in
theorem sealed_group_of (h : G1AddNegAlg) :
  ∀ (p : BLS12_381_G1_Element), InG1 p → (0 + (p + -p)) + 0 = 0 := by blaster

/-- The payoff, and the first fact about G1 *arithmetic* in this project that `blaster`
    proved: discharged from the real axioms, so the footprint names them and nothing else. -/
theorem sealed_group :
  ∀ (p : BLS12_381_G1_Element), InG1 p → (0 + (p + -p)) + 0 = 0 :=
  sealed_group_of g1AddNegAlg

/-! The footprint is the three real axioms and nothing else. Two things it does *not*
    contain: any artefact of the seal -- an `irreducible` attribute is not a proof step, so
    sealing is invisible to the kernel -- and `InG1_def`, because nothing here unfolded the
    guard. Sealing buys translatability at zero cost to the trust base, which is what makes
    it preferable to restating the laws over the `opaque` builtins (that route needs a
    definitional bridge axiom per operation). -/

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterSealed.sealed_group' depends on axioms: [propext,
 Quot.sound,
 Blaster.Tactic.blasterProven,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_add_comm,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_add_neg,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_add_zero]
-/
#guard_msgs in
#print axioms sealed_group

/-! The same shape on G2, to show the one seal covers both groups. -/

def G2AddNegAlg : Prop :=
  (∀ (x y : BLS12_381_G2_Element), x + y = y + x) ∧
  (∀ (x : BLS12_381_G2_Element), x + 0 = x) ∧
  (∀ (x : BLS12_381_G2_Element), InG2 x → x + -x = 0)

theorem g2AddNegAlg : G2AddNegAlg := ⟨g2_add_comm, g2_add_zero, g2_add_neg⟩

set_option warn.sorry false in
theorem sealed_group_g2_of (h : G2AddNegAlg) :
  ∀ (p : BLS12_381_G2_Element), InG2 p → (0 + (p + -p)) + 0 = 0 := by blaster

/-! ## The scalar action, including the huge modulus

    `g1_scalarMul_mod` compares against `r`, a 255-bit constant, which was the suspected
    reason the full bundle stalls. It is not: adding it to the premise leaves the goal
    `Valid`. -/

set_option warn.sorry false in
theorem sealed_smul_of
    (h : (∀ (x : BLS12_381_G1_Element), (1 : Int) * x = x) ∧
         (∀ (x y : BLS12_381_G1_Element), x + y = y + x) ∧
         (∀ (x : BLS12_381_G1_Element) (i : Int), InG1 x → (i % r) * x = i * x)) :
  ∀ (p q : BLS12_381_G1_Element), (1 : Int) * (p + q) = q + p := by blaster

/-! ## The limit, pinned as a limit

    The same goal as `sealed_smul_of`, from the whole twelve-conjunct `G1Alg` instead of the
    three laws it needs. `Undetermined`: the premise set is too large for the solver, not
    untranslatable. Pinned so that a future improvement -- a Blaster bump, or a better
    encoding -- shows up here as a failing expectation rather than going unnoticed. -/

#blaster (timeout: 30) (solve-result: 2) [G1Alg →
  ∀ (p q : BLS12_381_G1_Element), InG1 p → InG1 q → (1 : Int) * (p + q) = q + p]

/-! ## The vacuity guards

    Both must stay `Undetermined`. A `Valid` here means the encoded premise set is
    contradictory and every sealed result above is worthless. -/

#blaster (timeout: 30) (solve-result: 2) [G1AddNegAlg → False]

#blaster (timeout: 30) (solve-result: 2) [G1Alg →
  ∀ (p q : BLS12_381_G1_Element), p + q = p]

end PlutusCore.Crypto.BLS12_381.Tests.AxiomsBlasterSealed
