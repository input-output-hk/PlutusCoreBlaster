import Cryptograph.BLS12_381

import PlutusCore.ByteString
import PlutusCore.Integer
import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2

namespace PlutusCore.Crypto.BLS12_381.Pairing

open Cryptograph.BLS12_381
open Cryptograph.BLS12_381 (Fq6 Fq12)
open PlutusCore.Integer PlutusCore.ByteString
open PlutusCore.Crypto.BLS12_381.G1 PlutusCore.Crypto.BLS12_381.G2

/-! ## Formalisation for PlutusCore BLS12_381_MlResult representation and builtin functions. -/

namespace Internal

open Lean (ToExpr toExpr mkApp2 mkApp3)

abbrev BLS12_381_MlResult := Option (Fq12)

instance : ToExpr Fq6 where
  toTypeExpr := .const ``Fq6 []
  toExpr x   := mkApp3 (.const ``Fq6.mk []) (toExpr x.v2) (toExpr x.v1) (toExpr x.v0)

instance : ToExpr Fq12 where
  toTypeExpr := .const ``Fq12 []
  toExpr x   := (mkApp2 (.const ``Fq12.mk []) (toExpr x.w1) (toExpr x.w0))

opaque bls12_381_millerLoop (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element) : BLS12_381_MlResult :=
  calculateMillerLoop p q

opaque bls12_381_mulMlResult (x y : BLS12_381_MlResult) : BLS12_381_MlResult := (· * ·) <$> x <*> y

opaque bls12_381_finalVerify (x y : BLS12_381_MlResult) : Bool := .some true = finalVerify <$> x <*> y

end Internal

export Internal
  ( -- types
    BLS12_381_MlResult
    -- functions
    bls12_381_millerLoop
    bls12_381_mulMlResult
    bls12_381_finalVerify
  )

end PlutusCore.Crypto.BLS12_381.Pairing
