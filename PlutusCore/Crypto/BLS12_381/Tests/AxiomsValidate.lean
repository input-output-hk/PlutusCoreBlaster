import PlutusCore.Crypto.BLS12_381

namespace PlutusCore.Crypto.BLS12_381.Tests.AxiomsValidate

open Cryptograph.BLS12_381 (Point Fq1 Fq2 g1 g2)
open Cryptograph.BLS12_381.Internal (isOnCurve isInSubGroup Fq1.findY)

open PlutusCore.ByteString
open PlutusCore.Crypto.BLS12_381
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Crypto.BLS12_381.Pairing
open PlutusCore.Crypto.BLS12_381.Axioms

/-!
  # Numeric validation of the BLS12_381 axioms

  Every axiom of `Crypto/BLS12_381/Axioms.lean` that mentions an *evaluable* operation is
  sampled here against the `Cryptograph` implementation and against the vectors of the
  Plutus conformance suite, under
  `test-cases/uplc/evaluation/builtin/semantics/bls12_381_*`.  `opaque` definitions still
  compile, so `#guard` runs the real builtin; `#guard` is a command with no proof term, which
  is why it is used here rather than `native_decide` -- nothing in this file reaches the
  kernel, so `Lean.ofReduceBool` stays out of the project's trust base.

  Three things this file is not.

  It is not the conformance suite.  `Tests/Conformance/Generated/Builtin/Semantics/Bls12_381_*`
  runs the same vectors end to end through the CEK machine and covers far more of them, but
  is built only by the manual `ci-conformance` workflow.  What is here is a guard per axiom,
  in the default build, labelled with the axiom it samples.

  It is not a proof.  `#guard` uses the untrusted evaluator; an axiom that survives every
  guard below is still an axiom.

  It is not exhaustive, and cannot be.  `g1_dlog`, `g2_dlog`, `e`, `pi` and `MlOk` are
  uninterpreted -- axioms of function or predicate type, with no code -- so an axiom phrased
  over them is sampled through an observable consequence instead, and each case below says
  which.  `pi_millerLoop` is the one axiom with no observable form at all: it relates two
  uninterpreted symbols and mentions no evaluable operation on either side.
-/

/-! ## Hex, as the conformance `.uplc` files spell it

    A `ByteString` is a `String` of one `Char` per byte -- `Char.toUInt8` and `Char.ofUInt8`
    are the correspondence the builtins themselves use -- so a vector is a hex string decoded
    two characters at a time.  Pasting the conformance hex verbatim is what makes a
    transcription error visible, and the length guards below are what catch one. -/

private def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else (c.toNat ||| 0x20) - 87

private def hexBytes : List Char → List Char
  | hi :: lo :: t => Char.ofNat (16 * hexVal hi + hexVal lo) :: hexBytes t
  | _             => []

/-- An even-length hex string, no `0x` prefix and no separators, as a `ByteString`. -/
private def bs (h : String) : ByteString := ⟨⟨hexBytes h.data⟩⟩

#guard (hexVal '0', hexVal '9', hexVal 'a', hexVal 'f', hexVal 'A', hexVal 'F')
       == (0, 9, 10, 15, 10, 15)
#guard (bs "00ff10").data.data == [Char.ofNat 0, Char.ofNat 255, Char.ofNat 16]

/-! ## Vectors

    Compressed forms come from the conformance suite, named after the case they are taken
    from.  Affine points are multiples of the generators, whose subgroup membership is
    `InG1_smul_gen` rather than an assumption. -/

/-- `bls12_381_G1_uncompress/zero`: the compressed identity. -/
private def g1ZeroHex : String :=
  "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
/-- `bls12_381_G1_uncompress/on-curve-bit3-set`: `0x0102030405` hashed to G1. -/
private def g1SignSetHex : String :=
  "a1e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb"
/-- `on-curve-bit3-clear`: the same x-coordinate with the sign bit cleared, which selects the
    other root -- i.e. the negation of the point above. -/
private def g1SignClearHex : String :=
  "81e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb"
/-- `on-curve-bit1-clear`: the compression bit cleared. -/
private def g1NoCompressHex : String :=
  "21e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb"
/-- `off-curve`: not the x-coordinate of any point of E1. -/
private def g1OffCurveHex : String :=
  "a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003"
/-- `out-of-group`: on E1, but not in the order-r subgroup. -/
private def g1OutOfGroupHex : String :=
  "a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005"
/-- `bad-zero-01`: compression bit clear, infinity bit set. -/
private def g1BadZeroHex : String :=
  "400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
/-- `too-short`: the compressed identity, truncated to 47 bytes. -/
private def g1TooShortHex : String :=
  "c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

/-- `bls12_381_G2_uncompress/zero`. -/
private def g2ZeroHex : String :=
  "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000\
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

/-! The sizes the vectors are meant to have.  A mis-pasted hex string fails here, before it
    can fail something more interesting. -/

#guard (bs g1ZeroHex       ).length == 48
#guard (bs g1SignSetHex    ).length == 48
#guard (bs g1SignClearHex  ).length == 48
#guard (bs g1NoCompressHex ).length == 48
#guard (bs g1OffCurveHex   ).length == 48
#guard (bs g1OutOfGroupHex ).length == 48
#guard (bs g1BadZeroHex    ).length == 48
#guard (bs g1TooShortHex   ).length == 47
#guard (bs g2ZeroHex       ).length == 96

/-! ### Affine samples

    `p₁ p₂ p₃`, `q₁ q₂ q₃` are multiples of the generators, so `InG1_smul_gen` /
    `InG2_smul_gen` discharge every `InG1`/`InG2` guard on them.

    `outOfGroup` is the `out-of-group` conformance x-coordinate lifted to a point: on the
    curve, so the scalar ladder is well behaved on it, but not in the order-r subgroup.  That
    is what the *unguarded* axioms have to hold of, and what `InG1_def` has to exclude.  (An
    off-curve point would not do: it can drive `binaryInversion 0`, which panics.) -/

private def p₁ : BLS12_381_G1_Element := ( 2 : Int) * g1
private def p₂ : BLS12_381_G1_Element := ( 3 : Int) * g1
private def p₃ : BLS12_381_G1_Element := ( 5 : Int) * g1
private def q₁ : BLS12_381_G2_Element := ( 2 : Int) * g2
private def q₂ : BLS12_381_G2_Element := ( 3 : Int) * g2
private def q₃ : BLS12_381_G2_Element := ( 5 : Int) * g2

private def outOfGroup : BLS12_381_G1_Element :=
  match Fq1.findY (Cryptograph.BLS12_381.Internal.Fq1.ofNat 5) false with
  | some y => .affine (Cryptograph.BLS12_381.Internal.Fq1.ofNat 5) y
  | none   => zeroG1

#guard isOnCurve    outOfGroup
#guard isInSubGroup outOfGroup == false

/-! `0` in the axioms is the `Zero` instance of `Axioms.lean`, i.e. `zeroG1`/`zeroG2`. -/
#guard (0 : BLS12_381_G1_Element) == zeroG1
#guard (0 : BLS12_381_G2_Element) == zeroG2

/-! ## The `opaque` builtins against the `Cryptograph` operations

    The group axioms are stated over the `Cryptograph` `+`/`*`/`-`, while the builtins are
    `opaque`, so no proof in this project can see that the two agree.  Evaluation is the only
    way to observe it, which makes these guards the seam that licenses reading `G1Alg` and
    `G2Alg` as facts about the builtins. -/

#guard bls12_381_G1_add       p₁ p₂ == p₁ + p₂
#guard bls12_381_G1_neg       p₁    == -p₁
#guard bls12_381_G1_scalarMul 19 p₁ == (19 : Int) * p₁
#guard bls12_381_G1_equal     p₁ p₁ == true
#guard bls12_381_G1_equal     p₁ p₂ == false

#guard bls12_381_G2_add       q₁ q₂ == q₁ + q₂
#guard bls12_381_G2_neg       q₁    == -q₁
#guard bls12_381_G2_scalarMul 19 q₁ == (19 : Int) * q₁
#guard bls12_381_G2_equal     q₁ q₁ == true
#guard bls12_381_G2_equal     q₁ q₂ == false

/-! ## The unguarded laws

    `g1_scalarMul_zero`, `g1_scalarMul_one`, `g1_scalarMul_neg`, `g1_add_zero`, `g1_add_comm`,
    and `g2_scalarMul_zero`, `g2_scalarMul_one`, `g2_scalarMul_neg`, `g2_add_zero`,
    `g2_add_comm`.  Unguarded in `Axioms.lean`, so sampled off the subgroup and at the identity
    as well as on it: `pointAdd` matches `.infinity` structurally and is symmetric in its
    arguments, which is the claim, and these are the samples. -/

#guard (( 0 : Int) * p₁        ) == zeroG1
#guard (( 0 : Int) * outOfGroup) == zeroG1
#guard (( 0 : Int) * zeroG1    ) == zeroG1
#guard (( 1 : Int) * p₁        ) == p₁
#guard (( 1 : Int) * outOfGroup) == outOfGroup
#guard (( 1 : Int) * zeroG1    ) == zeroG1
#guard ((-1 : Int) * p₁        ) == -p₁
#guard ((-1 : Int) * outOfGroup) == -outOfGroup

#guard (p₁         + zeroG1) == p₁
#guard (outOfGroup + zeroG1) == outOfGroup
#guard (zeroG1     + zeroG1) == (zeroG1 : BLS12_381_G1_Element)

#guard (p₁ + p₂        ) == (p₂ + p₁)
#guard (outOfGroup + p₁) == (p₁ + outOfGroup)

#guard (( 0 : Int) * q₁) == zeroG2
#guard (( 1 : Int) * q₁) == q₁
#guard ((-1 : Int) * q₁) == -q₁
#guard (q₁ + zeroG2)     == q₁
#guard (q₁ + q₂)         == (q₂ + q₁)

/-! ## `g1_add_neg`, `g1_add_assoc`, and their G2 counterparts

    `g2_add_neg` and `g2_add_assoc` are sampled in the same lines.  All four are
    `InG1`/`InG2`-guarded.  The guard on `add_neg` is real.  The guard on `add_assoc` is
    conservative -- associativity is a fact about the whole curve -- and the last guard below
    pins that, so a future weakening of the axiom has a sample to point at. -/

#guard (p₁ + -p₁) == zeroG1
#guard (q₁ + -q₁) == zeroG2

#guard ((p₁ + p₂) + p₃) == (p₁ + (p₂ + p₃))
#guard ((q₁ + q₂) + q₃) == (q₁ + (q₂ + q₃))
#guard ((outOfGroup + p₁) + p₂) == (outOfGroup + (p₁ + p₂))

/-! ### Independently: a compressed point's sign bit negates the point

    `on-curve-bit3-set` and `on-curve-bit3-clear` are one x-coordinate with and without the
    sign bit, i.e. a point and its negation, sourced by hashing rather than from the
    generator.  One guard for `g1_add_neg` and `g1_scalarMul_neg` at once. -/

#guard match bls12_381_G1_uncompress (bs g1SignSetHex),
             bls12_381_G1_uncompress (bs g1SignClearHex) with
       | .ok a, .ok b => (a + b == zeroG1) && (((-1 : Int) * a) == b) && (a != b)
       | _,     _     => false

/-! ## The ℤ/r-module laws

    Conformance `mul19+25` (`g1_scalarMul_add_scalar`), `muladd`/`addmul`
    (`g1_scalarMul_add_point`, at n = 2157) and `mul4x-11` (`g1_scalarMul_mul`), then the same
    three for `g2_scalarMul_add_scalar`, `g2_scalarMul_add_point` and `g2_scalarMul_mul`. -/

#guard ((19 + 25 : Int) * p₁) == (((19 : Int) * p₁) + ((25 : Int) * p₁))
#guard ((2157 : Int) * (p₁ + p₂)) == (((2157 : Int) * p₁) + ((2157 : Int) * p₂))
#guard ((4 * 11 : Int) * p₁) == ((4 : Int) * ((11 : Int) * p₁))

#guard ((19 + 25 : Int) * q₁) == (((19 : Int) * q₁) + ((25 : Int) * q₁))
#guard ((2157 : Int) * (q₁ + q₂)) == (((2157 : Int) * q₁) + ((2157 : Int) * q₂))
#guard ((4 * 11 : Int) * q₁) == ((4 : Int) * ((11 : Int) * q₁))

/-! ## `g1_order`, `g2_order`, and `g1_scalarMul_mod`

    `Axioms.lean` *derives* `r * g1 = 0` from `g1_dlog_scalarMul` and
    `g1_dlog_emod_eq_zero_iff`, so it assumes nothing.  What no derivation can establish is
    that the `r` of `Axioms.lean` is the order of the generator of the curve `Cryptograph`
    implements.  That is this guard, and it is what lets the derivation replace the
    `decide +native` that used to sit inside the axiom module.

    Conformance `mulperiodic-01` states the same thing on a random point; `mulperiodic-02..04`
    are `g1_scalarMul_mod` and `g2_scalarMul_mod`, here at `n := r + 7`.  Note the `%`:
    `r : Int`, so this is `Int.emod` and `(r + 7) % r = 7`.  A `Nat` modulus under a coercion
    is not what the axiom says. -/

#guard (r * g1) == zeroG1
#guard (r * g2) == zeroG2

#guard (((r + 7) % r) * p₁) == ((r + 7) * p₁)
#guard (((r + 7) % r) * q₁) == ((r + 7) * q₁)

/-! ## `g1_dlog_scalarMul`, `g2_dlog_scalarMul`

    `g1_dlog` is `axiom g1_dlog : BLS12_381_G1_Element → Int`: no code, so no `#guard` can
    mention it.  What the axiom says beyond `g1_order` is that `n ↦ n * g1` factors through
    ℤ/r *injectively* -- the generator's order is exactly r, not a proper divisor of it --
    and that much is sampled. -/

#guard ((1 : Int) * g1) != zeroG1
#guard ((2 : Int) * g1) != zeroG1
#guard ((3 : Int) * g1) != zeroG1
#guard ((2 : Int) * g1) != ((3 : Int) * g1)
#guard ((1 : Int) * g2) != zeroG2
#guard ((2 : Int) * g2) != ((3 : Int) * g2)

/-! ## `InG1_def`, `InG2_def`

    `InG1` is `opaque … : Prop` -- deliberately, so the solver sees an uninterpreted
    predicate -- so there is nothing to evaluate.  What is checkable is that the body it was
    given, `∃ n : Int, a = n * g1`, describes the subgroup `Cryptograph` computes: every
    witness `InG1_smul_gen` supplies passes `isInSubGroup`, and a point on the curve but
    outside the subgroup does not. -/

#guard isInSubGroup g1
#guard isInSubGroup ((7 : Int) * g1)
#guard isInSubGroup (p₁ + p₂)
#guard isInSubGroup (zeroG1 : BLS12_381_G1_Element)
#guard isInSubGroup outOfGroup == false
#guard isInSubGroup g2
#guard isInSubGroup ((7 : Int) * g2)

/-! ## Serialisation

    `g1_uncompress_compress` and `g2_uncompress_compress` are the round trip from a point,
    `g1_compress_uncompress` the round trip from bytes on both sign-bit branches -- the
    direction that breaks first if `compress` picks the wrong root.  `g1_uncompress_subgroup` is `isInSubGroup` on what comes
    back; its sharpness is the negatives, every one of which the conformance suite expects to
    be an evaluation failure.

    The `out-of-group` rejection is not an accident of the vector: `Cryptograph.uncompress`
    gates on `isInSubGroup` before returning, which is the structural reason
    `g1_uncompress_subgroup` holds -- and the reason every `uncompress` here costs a 255-bit
    scalar multiplication. -/

#guard (bls12_381_G1_uncompress (bls12_381_G1_compress p₁    )).toOption == some p₁
#guard (bls12_381_G1_uncompress (bls12_381_G1_compress zeroG1)).toOption == some zeroG1
#guard (bls12_381_G2_uncompress (bls12_381_G2_compress q₁    )).toOption == some q₁
#guard (bls12_381_G2_uncompress (bls12_381_G2_compress zeroG2)).toOption == some zeroG2

/-! `g1_compress_uncompress` / `g2_compress_uncompress`: the round trip from bytes, and
    `g1_uncompress_subgroup` / `g2_uncompress_subgroup` on what comes back. -/

#guard match bls12_381_G2_uncompress (bs g2ZeroHex) with
       | .ok q    => bls12_381_G2_compress q == bs g2ZeroHex && isInSubGroup q
       | .error _ => false

#guard (bls12_381_G1_uncompress (bs g1ZeroHex)).toOption == some zeroG1
#guard (bls12_381_G2_uncompress (bs g2ZeroHex)).toOption == some zeroG2

#guard match bls12_381_G1_uncompress (bs g1SignSetHex) with
       | .ok p    => bls12_381_G1_compress p == bs g1SignSetHex && isInSubGroup p
       | .error _ => false
#guard match bls12_381_G1_uncompress (bs g1SignClearHex) with
       | .ok p    => bls12_381_G1_compress p == bs g1SignClearHex && isInSubGroup p
       | .error _ => false

#guard (bls12_381_G1_uncompress (bs g1OutOfGroupHex)).toOption == none
#guard (bls12_381_G1_uncompress (bs g1OffCurveHex  )).toOption == none
#guard (bls12_381_G1_uncompress (bs g1NoCompressHex)).toOption == none
#guard (bls12_381_G1_uncompress (bs g1BadZeroHex   )).toOption == none
#guard (bls12_381_G1_uncompress (bs g1TooShortHex  )).toOption == none

/-! ## The `MlResult` layer

    `MlOk` is `axiom MlOk : BLS12_381_MlResult → Prop`: uninterpreted, so unevaluable.  Its
    intended extension is `some x`, and `Option.isSome` is the surrogate.  The guards on
    `none` are what the domain restriction is *for*: `millerLoop` returns `none` at either
    identity, `mulMlResult` absorbs it, and `finalVerify` reports it as a hard `false`.  All
    of them are free -- the Miller loop short-circuits on its first iteration. -/

private def m₁ : BLS12_381_MlResult := bls12_381_millerLoop p₁ q₁
private def m₂ : BLS12_381_MlResult := bls12_381_millerLoop p₂ q₁

#guard m₁.isSome && m₂.isSome                                              -- `millerLoop_ok`
#guard (bls12_381_millerLoop zeroG1 q₁).isNone                             -- and its sharpness
#guard (bls12_381_millerLoop p₁ zeroG2).isNone
#guard (bls12_381_mulMlResult (bls12_381_millerLoop zeroG1 q₁) m₁).isNone   -- `mulMlResult_ok_inv`
#guard (bls12_381_mulMlResult m₁ m₂).isSome                                -- `mulMlResult_ok`
#guard bls12_381_finalVerify (bls12_381_millerLoop zeroG1 q₁) m₁ == false   -- `finalVerify_ok`

/-! `mulMlResult_comm` and `mulMlResult_assoc`, on real Miller-loop values.  Exact Fq12
    arithmetic with no domain restriction, and cheap: no final exponentiation. -/

#guard bls12_381_mulMlResult m₁ m₂ == bls12_381_mulMlResult m₂ m₁
#guard bls12_381_mulMlResult (bls12_381_mulMlResult m₁ m₂) m₁
       == bls12_381_mulMlResult m₁ (bls12_381_mulMlResult m₂ m₁)

/-! ## The pairing, through `finalVerify`

    `pi` and `e` are uninterpreted, so `pi_millerLoop` has no numeric content: it relates two
    symbols, neither of which has code.  What *is* observable is the composite
    `finalVerify (ml _ _) (ml _ _)`, which by `finalVerify_sound`/`_complete` and
    `pi_millerLoop` decides `e _ _ = e _ _`.

    Three instances, and no fewer: the positive, the negative that stops the positive being
    vacuous, and the bilinear one.  Each costs one final exponentiation, so conformance
    `balanced` and `right-additive` are left to the conformance suite.

    These are also the only observable trace of `e_dlog` and `e_nondegen`.  `e_dlog`'s content
    -- that `e p q` depends only on the product of the two discrete logs -- shows up as the
    bilinear guard; `e_nondegen`'s, that the identity of `G_T` is reached only at a zero
    argument, shows up as the `isNone` guards above, since the Miller loop never produces a
    value at either identity for `finalVerify` to accept. -/

/-! `equal-pairing`: `finalVerify_complete`, and `finalVerify_millerLoop_pair` at `p = p'`. -/
#guard bls12_381_finalVerify m₁ m₁ == true

/-! Sharpness.  Without this the two guards around it would be satisfied by a `finalVerify`
    that is constantly `true`, and `finalVerify_sound` would be saying nothing. -/
#guard bls12_381_finalVerify m₁ m₂ == false

/-! `left-additive`, i.e. `millerLoop_add_left_upto_finalVerify` -- and through it
    `pi_mulMlResult`, `e_add_left` and `finalVerify_complete` at once. -/
#guard bls12_381_finalVerify
         (bls12_381_millerLoop (p₁ + p₂) q₁)
         (bls12_381_mulMlResult m₁ m₂) == true

end PlutusCore.Crypto.BLS12_381.Tests.AxiomsValidate
