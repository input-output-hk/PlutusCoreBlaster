import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing

import PlutusCore.Crypto.Hash
import PlutusCore.Crypto.Ed25519
import PlutusCore.Crypto.Secp256k1
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils

namespace PlutusCore.UPLC.BuiltinFunctions.Crypto

namespace PLC
  open PlutusCore.Crypto.Hash
  export PlutusCore.Crypto.Hash
    (
      sha2_256
      sha3_256
      blake2b_224
      blake2b_256
      keccak_256
      ripemd_160
    )
  open PlutusCore.Crypto.Ed25519
  export PlutusCore.Crypto.Ed25519
    (
      verifyEd25519Signature
    )
  open PlutusCore.Crypto.Secp256k1
  export PlutusCore.Crypto.Secp256k1
    (
      verifyEcdsaSecp256k1Signature
      verifySchnorrSecp256k1Signature
    )
  open PlutusCore.Crypto.BLS12_381.G1
  export PlutusCore.Crypto.BLS12_381.G1
    (
      bls12_381_G1_add
      bls12_381_G1_neg
      bls12_381_G1_scalarMul
      bls12_381_G1_equal
      bls12_381_G1_hashToGroup
      bls12_381_G1_compress
      bls12_381_G1_uncompress
    )
  open PlutusCore.Crypto.BLS12_381.G2
  export PlutusCore.Crypto.BLS12_381.G2
    (
      bls12_381_G2_add
      bls12_381_G2_neg
      bls12_381_G2_scalarMul
      bls12_381_G2_equal
      bls12_381_G2_hashToGroup
      bls12_381_G2_compress
      bls12_381_G2_uncompress
    )
  open PlutusCore.Crypto.BLS12_381.Pairing
  export PlutusCore.Crypto.BLS12_381.Pairing
    (
      bls12_381_millerLoop
      bls12_381_mulMlResult
      bls12_381_finalVerify
    )
end PLC

open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.BuiltinFunctions.Utils
open PlutusCore.Crypto.BLS12_381.G1 (BLS12_381_G1_Element)
open PlutusCore.Crypto.BLS12_381.G2 (BLS12_381_G2_Element)
open PlutusCore.Integer (Integer)

-- Hash functions

def sha2_256 : List CekValue → Option CekValue
  | [.VCon (.ByteString b)] => .some (PLC.sha2_256 b |> .ByteString |> .VCon)
  | _ => none

def sha3_256 : List CekValue → Option CekValue
  | [.VCon (.ByteString b)] => .some (PLC.sha3_256 b |> .ByteString |> .VCon)
  | _ => none

def blake2b_256 : List CekValue → Option CekValue
  | [.VCon (.ByteString b)] => .some (PLC.blake2b_256 b |> .ByteString |> .VCon)
  | _ => none

def blake2b_224 : List CekValue → Option CekValue
  | [.VCon (.ByteString b)] => .some (PLC.blake2b_224 b |> .ByteString |> .VCon)
  | _ => none

def keccak_256 : List CekValue → Option CekValue
  | [.VCon (.ByteString b)] => .some (PLC.keccak_256 b |> .ByteString |> .VCon)
  | _ => none

def ripemd_160 : List CekValue → Option CekValue
  | [.VCon (.ByteString b)] => .some (PLC.ripemd_160 b |> .ByteString |> .VCon)
  | _ => none

-- Signature verification functions

-- CEK args are reversed: [sig, msg, pk] for f(pk, msg, sig)
-- Returns none (→ EvaluationError) for invalid lengths or unparseable key/sig.
def verifyEd25519Signature : List CekValue → Option CekValue
  | [.VCon (.ByteString sig), .VCon (.ByteString msg), .VCon (.ByteString pk)] =>
    tryCatchSome (PLC.verifyEd25519Signature pk msg sig) (CekValue.VCon ∘ Const.Bool)
  | _ => none

def verifyEcdsaSecp256k1Signature : List CekValue → Option CekValue
  | [.VCon (.ByteString sig), .VCon (.ByteString msg), .VCon (.ByteString pk)] =>
    tryCatchSome (PLC.verifyEcdsaSecp256k1Signature pk msg sig) (CekValue.VCon ∘ Const.Bool)
  | _ => none

def verifySchnorrSecp256k1Signature : List CekValue → Option CekValue
  | [.VCon (.ByteString sig), .VCon (.ByteString msg), .VCon (.ByteString pk)] =>
    tryCatchSome (PLC.verifySchnorrSecp256k1Signature pk msg sig) (CekValue.VCon ∘ Const.Bool)
  | _ => none

-- BLS12-381 functions

def bls12381G1Add : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G1_element x), .VCon (.Bls12_381_G1_element y)] => PLC.bls12_381_G1_add x y |> .Bls12_381_G1_element |> .VCon |> .some
  | _ => none

def bls12381G1Neg : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G1_element x)] => PLC.bls12_381_G1_neg x |> .Bls12_381_G1_element |> .VCon |> .some
  | _ => none

def bls12381G1ScalarMul : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G1_element y), .VCon (.Integer x)] => PLC.bls12_381_G1_scalarMul x y |> .Bls12_381_G1_element |> .VCon |> .some
  | _ => none

def bls12381G1Equal : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G1_element x), .VCon (.Bls12_381_G1_element y)] => PLC.bls12_381_G1_equal x y |> .Bool |> .VCon |> .some
  | _ => none

def bls12381G1HashToGroup : List CekValue → Option CekValue
  | [.VCon (.ByteString dst), .VCon (.ByteString msg)] => (.VCon ∘ .Bls12_381_G1_element) <$> (PLC.bls12_381_G1_hashToGroup msg dst |> Except.toOption)
  | _ => none

def bls12381G1Compress : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G1_element x)] => PLC.bls12_381_G1_compress x |> .ByteString |> .VCon |> .some
  | _ => none

def bls12381G1Uncompress : List CekValue → Option CekValue
  | [.VCon (.ByteString x)] => (.VCon ∘ .Bls12_381_G1_element) <$> (PLC.bls12_381_G1_uncompress x |> Except.toOption)
  | _ => none

def bls12381G2Add : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G2_element x), .VCon (.Bls12_381_G2_element y)] => PLC.bls12_381_G2_add x y |> .Bls12_381_G2_element |> .VCon |> .some
  | _ => none

def bls12381G2Neg : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G2_element x)] => PLC.bls12_381_G2_neg x |> .Bls12_381_G2_element |> .VCon |> .some
  | _ => none

def bls12381G2ScalarMul : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G2_element y), .VCon (.Integer x)] => PLC.bls12_381_G2_scalarMul x y |> .Bls12_381_G2_element |> .VCon |> .some
  | _ => none

def bls12381G2Equal : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G2_element x), .VCon (.Bls12_381_G2_element y)] => PLC.bls12_381_G2_equal x y |> .Bool |> .VCon |> .some
  | _ => none

def bls12381G2HashToGroup : List CekValue → Option CekValue
  | [.VCon (.ByteString dst), .VCon (.ByteString msg)] => (.VCon ∘ .Bls12_381_G2_element) <$> (PLC.bls12_381_G2_hashToGroup msg dst |> Except.toOption)
  | _ => none

def bls12381G2Compress : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G2_element x)] => PLC.bls12_381_G2_compress x |> .ByteString |> .VCon |> .some
  | _ => none

def bls12381G2Uncompress : List CekValue → Option CekValue
  | [.VCon (.ByteString x)] => (.VCon ∘ .Bls12_381_G2_element) <$> (PLC.bls12_381_G2_uncompress x |> Except.toOption)
  | _ => none

-- MSM scalar bound: -2^4095 ≤ s < 2^4095
private def msmScalarInBounds (n : Int) : Bool :=
  let bound : Int := (2 : Int) ^ (4095 : Nat)
  n ≥ -bound && n < bound

def bls12381G1MultiScalarMul : List CekValue → Option CekValue
  | [.VCon (.ConstList points), .VCon (.ConstList scalars)] => do
    let scalarsI ← scalars.mapM (fun c => match c with | .Integer n => some n | _ => none)
    let pointsG1 ← points.mapM (fun c => match c with | .Bls12_381_G1_element p => some p | _ => none)
    if scalarsI.any (fun n => !msmScalarInBounds n) then none
    else
      let result := (List.zip scalarsI pointsG1).foldl
        (fun acc (n, p) => PLC.bls12_381_G1_add acc (PLC.bls12_381_G1_scalarMul n p))
        (default : BLS12_381_G1_Element)
      some (.VCon (.Bls12_381_G1_element result))
  | _ => none

def bls12381G2MultiScalarMul : List CekValue → Option CekValue
  | [.VCon (.ConstList points), .VCon (.ConstList scalars)] => do
    let scalarsI ← scalars.mapM (fun c => match c with | .Integer n => some n | _ => none)
    let pointsG2 ← points.mapM (fun c => match c with | .Bls12_381_G2_element p => some p | _ => none)
    if scalarsI.any (fun n => !msmScalarInBounds n) then none
    else
      let result := (List.zip scalarsI pointsG2).foldl
        (fun acc (n, p) => PLC.bls12_381_G2_add acc (PLC.bls12_381_G2_scalarMul n p))
        (default : BLS12_381_G2_Element)
      some (.VCon (.Bls12_381_G2_element result))
  | _ => none

def bls12381MillerLoop : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_G2_element y), .VCon (.Bls12_381_G1_element x)] => PLC.bls12_381_millerLoop x y |> .Bls12_381_MlResult |> .VCon |> .some
  | _ => none

def bls12381MulMlResult : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_MlResult x), .VCon (.Bls12_381_MlResult y)] => PLC.bls12_381_mulMlResult x y |> .Bls12_381_MlResult |> .VCon |> .some
  | _ => none

def bls12381FinalVerify : List CekValue → Option CekValue
  | [.VCon (.Bls12_381_MlResult x), .VCon (.Bls12_381_MlResult y)] => PLC.bls12_381_finalVerify x y |> .Bool |> .VCon |> .some
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.Crypto
