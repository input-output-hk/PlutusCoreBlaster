import Cryptograph.BLS12_381
import Cryptograph.String

import PlutusCore.ByteString
import PlutusCore.Integer

namespace PlutusCore.Crypto.BLS12_381.G1

open Lean (ToExpr toExpr mkApp2 mkApp3)

open Cryptograph.BLS12_381 (Point Fq1)
open Cryptograph.BLS12_381 Cryptograph.String
open PlutusCore.Integer PlutusCore.ByteString

/-! ## Formalisation for PlutusCore BLS12_381_G1_Element representation and builtin functions. -/

namespace Internal

abbrev BLS12_381_G1_Element := Point Fq1

instance : ToExpr Fq1 where
  toTypeExpr := .const ``Fq1 []
  toExpr x   := .app (.const ``Fq1.mk []) (toExpr x.t)

instance : ToExpr BLS12_381_G1_Element where
  toTypeExpr := .const ``BLS12_381_G1_Element []
  toExpr
    | .infinity   => .app (.const ``Point.infinity []) (ToExpr.toTypeExpr (α := Fq1))
    | .affine x y => mkApp3 (.const ``Point.affine []) (ToExpr.toTypeExpr (α := Fq1)) (toExpr x) (toExpr y)

opaque bls12_381_G1_add (x y : BLS12_381_G1_Element) : BLS12_381_G1_Element := x + y
opaque bls12_381_G1_neg (x : BLS12_381_G1_Element) : BLS12_381_G1_Element := -x
opaque bls12_381_G1_scalarMul (z : Integer) (x : BLS12_381_G1_Element) : BLS12_381_G1_Element := z * x
opaque bls12_381_G1_equal (x y : BLS12_381_G1_Element) : Bool := x = y

opaque bls12_381_G1_hashToGroup (msg dst : ByteString) : Except String BLS12_381_G1_Element :=
  match Fq1.hashToCurve (Char.toUInt8 <$> msg.data.data) (Char.toUInt8 <$> dst.data.data) with
  | .some r => .ok r
  | .none   => .error "bls12_381_G1_hashToGroup: Domain separator tag too long!"

opaque bls12_381_G1_compress (p : BLS12_381_G1_Element) : ByteString := ⟨⟨Char.ofUInt8 <$> compressG1 p⟩⟩

opaque bls12_381_G1_uncompress (b : ByteString) : Except String BLS12_381_G1_Element :=
  match uncompressG1 (Char.toUInt8 <$> b.data.data) with
  | .some r => .ok r
  | .none   => .error "bls12_381_G1_uncompress: invalid point"

end Internal

export Internal
  ( -- types
    BLS12_381_G1_Element
    -- functions
    bls12_381_G1_add
    bls12_381_G1_neg
    bls12_381_G1_scalarMul
    bls12_381_G1_equal
    bls12_381_G1_hashToGroup
    bls12_381_G1_compress
    bls12_381_G1_uncompress
  )

end PlutusCore.Crypto.BLS12_381.G1
