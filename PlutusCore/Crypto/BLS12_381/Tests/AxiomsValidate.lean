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
-/

/-! ## Hex, as the conformance `.uplc` files spell it -/

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

/-! ## Vectors -/

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
    off-curve point would not do: it can drive `binaryInversion 0`, which has no inverse to
    hand back.) -/

private def p₁ : BLS12_381_G1_Element := (2 : Int) * g1
private def p₂ : BLS12_381_G1_Element := (3 : Int) * g1
private def p₃ : BLS12_381_G1_Element := (5 : Int) * g1
private def q₁ : BLS12_381_G2_Element := (2 : Int) * g2
private def q₂ : BLS12_381_G2_Element := (3 : Int) * g2
private def q₃ : BLS12_381_G2_Element := (5 : Int) * g2

private def outOfGroup : BLS12_381_G1_Element :=
  match Fq1.findY (Cryptograph.BLS12_381.Internal.Fq1.ofNat 5) false with
  | some y => .affine (Cryptograph.BLS12_381.Internal.Fq1.ofNat 5) y
  | none   => zeroG1

#guard isOnCurve    outOfGroup
#guard isInSubGroup outOfGroup == false

/-! `0` in the axioms is the `Zero` instance of `Axioms.lean`, i.e. `zeroG1`/`zeroG2`. -/
#guard (0 : BLS12_381_G1_Element) == zeroG1
#guard (0 : BLS12_381_G2_Element) == zeroG2

/-! ## The `opaque` builtins against the `Cryptograph` operations -/

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

/-! ## The unguarded laws -/

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

/-! ## `g1_add_neg`, `g1_add_assoc`, and their G2 counterparts -/

#guard (p₁ + -p₁) == zeroG1
#guard (q₁ + -q₁) == zeroG2

#guard ((p₁ + p₂) + p₃) == (p₁ + (p₂ + p₃))
#guard ((q₁ + q₂) + q₃) == (q₁ + (q₂ + q₃))
#guard ((outOfGroup + p₁) + p₂) == (outOfGroup + (p₁ + p₂))

/-! ### Independently: a compressed point's sign bit negates the point -/

#guard match bls12_381_G1_uncompress (bs g1SignSetHex), bls12_381_G1_uncompress (bs g1SignClearHex) with
       | .ok a, .ok b => (a + b == zeroG1) && (((-1 : Int) * a) == b) && (a != b)
       | _,     _     => false

/-! ## The ℤ/r-module laws -/

#guard ((19 + 25 : Int) * p₁)     == (((19 : Int) * p₁) + ((25 : Int) * p₁))
#guard ((2157 : Int) * (p₁ + p₂)) == (((2157 : Int) * p₁) + ((2157 : Int) * p₂))
#guard ((4 * 11 : Int) * p₁)      == ((4 : Int) * ((11 : Int) * p₁))

#guard ((19 + 25 : Int) * q₁)     == (((19 : Int) * q₁) + ((25 : Int) * q₁))
#guard ((2157 : Int) * (q₁ + q₂)) == (((2157 : Int) * q₁) + ((2157 : Int) * q₂))
#guard ((4 * 11 : Int) * q₁)      == ((4 : Int) * ((11 : Int) * q₁))

/-! ## `g1_order`, `g2_order`, and `g1_scalarMul_mod` -/

#guard (r * g1) == zeroG1
#guard (r * g2) == zeroG2

#guard (((r + 7) % r) * p₁) == ((r + 7) * p₁)
#guard (((r + 7) % r) * q₁) == ((r + 7) * q₁)

/-! ## `g1_dlog_scalarMul`, `g2_dlog_scalarMul` -/

#guard ((1 : Int) * g1) != zeroG1
#guard ((2 : Int) * g1) != zeroG1
#guard ((3 : Int) * g1) != zeroG1
#guard ((2 : Int) * g1) != ((3 : Int) * g1)
#guard ((1 : Int) * g2) != zeroG2
#guard ((2 : Int) * g2) != ((3 : Int) * g2)

/-! ## `InG1_def`, `InG2_def` -/

#guard isInSubGroup g1
#guard isInSubGroup ((7 : Int) * g1)
#guard isInSubGroup (p₁ + p₂)
#guard isInSubGroup (zeroG1 : BLS12_381_G1_Element)
#guard isInSubGroup outOfGroup == false
#guard isInSubGroup g2
#guard isInSubGroup ((7 : Int) * g2)

/-! ## Serialisation -/

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

/-! ## The `MlResult` layer -/

private def m₁ : BLS12_381_MlResult := bls12_381_millerLoop p₁ q₁
private def m₂ : BLS12_381_MlResult := bls12_381_millerLoop p₂ q₁

#guard m₁.isSome && m₂.isSome                                              -- `millerLoop_ok`
#guard (bls12_381_millerLoop zeroG1 q₁).isNone                             -- and its sharpness
#guard (bls12_381_millerLoop p₁ zeroG2).isNone
#guard (bls12_381_mulMlResult (bls12_381_millerLoop zeroG1 q₁) m₁).isNone  -- `mulMlResult_ok_inv`
#guard (bls12_381_mulMlResult m₁ m₂).isSome                                -- `mulMlResult_ok`
#guard bls12_381_finalVerify (bls12_381_millerLoop zeroG1 q₁) m₁ == false  -- `finalVerify_ok`

#guard bls12_381_mulMlResult m₁ m₂ == bls12_381_mulMlResult m₂ m₁
#guard bls12_381_mulMlResult (bls12_381_mulMlResult m₁ m₂) m₁
       == bls12_381_mulMlResult m₁ (bls12_381_mulMlResult m₂ m₁)

/-! ## The pairing, through `finalVerify` -/

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
