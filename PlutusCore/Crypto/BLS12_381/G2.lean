import Cryptograph.BLS12_381
import Cryptograph.String

import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.ByteString
import PlutusCore.Integer

namespace PlutusCore.Crypto.BLS12_381.G2

open Lean (ToExpr toExpr mkApp2 mkApp3)

open Cryptograph.BLS12_381 (Point Fq2)
open Cryptograph.BLS12_381 Cryptograph.String
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Integer PlutusCore.ByteString

/-! ## Formalisation for PlutusCore BLS12_381_G2_Element representation and builtin functions. -/

namespace Internal

abbrev BLS12_381_G2_Element := Point Fq2

instance : ToExpr Fq2 where
  toTypeExpr := .const ``Fq2 []
  toExpr x   := mkApp2 (.const ``Fq2.mk []) (toExpr x.u1) (toExpr x.u0)

instance : ToExpr BLS12_381_G2_Element where
  toTypeExpr := .const ``BLS12_381_G2_Element []
  toExpr
    | .infinity   => .app (.const ``Point.infinity []) (ToExpr.toTypeExpr (α := Fq2))
    | .affine x y => mkApp3 (.const ``Point.affine []) (ToExpr.toTypeExpr (α := Fq2)) (toExpr x) (toExpr y)

opaque bls12_381_G2_add (x y : BLS12_381_G2_Element) : BLS12_381_G2_Element := x + y
opaque bls12_381_G2_neg (x : BLS12_381_G2_Element) : BLS12_381_G2_Element := -x
opaque bls12_381_G2_scalarMul (z : Integer) (x : BLS12_381_G2_Element) : BLS12_381_G2_Element := z * x
opaque bls12_381_G2_equal (x y : BLS12_381_G2_Element) : Bool := x = y

opaque bls12_381_G2_hashToGroup (msg dst : ByteString) : Except String BLS12_381_G2_Element :=
  match Fq2.hashToCurve (Char.toUInt8 <$> msg.data.data) (Char.toUInt8 <$> dst.data.data) with
  | .some r => .ok r
  | .none   => .error "bls12_381_G2_hashToGroup: Domain separator tag too long!"

opaque bls12_381_G2_compress (p : BLS12_381_G2_Element) : ByteString := ⟨⟨Char.ofUInt8 <$> compressG2 p⟩⟩

opaque bls12_381_G2_uncompress (b : ByteString) : Except String BLS12_381_G2_Element :=
  match uncompressG2 (Char.toUInt8 <$> b.data.data) with
  | .some r => .ok r
  | .none   => .error "bls12_381_G2_uncompress: invalid point"

end Internal

export Internal
  ( -- types
    BLS12_381_G2_Element
    -- functions
    bls12_381_G2_add
    bls12_381_G2_neg
    bls12_381_G2_scalarMul
    bls12_381_G2_equal
    bls12_381_G2_hashToGroup
    bls12_381_G2_compress
    bls12_381_G2_uncompress
  )

end PlutusCore.Crypto.BLS12_381.G2
