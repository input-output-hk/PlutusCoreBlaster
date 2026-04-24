import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing
import PlutusCore.Data

namespace PlutusCore.UPLC.Term

open PlutusCore.Crypto.BLS12_381.G1 (BLS12_381_G1_Element)
open PlutusCore.Crypto.BLS12_381.G2 (BLS12_381_G2_Element)
open PlutusCore.Crypto.BLS12_381.Pairing (BLS12_381_MlResult)
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

inductive AtomicType
  | TypeInteger
  | TypeByteString
  | TypeString
  | TypeBool
  | TypeUnit
  | TypeData
  | TypeBls12_381_G1_element
  | TypeBls12_381_G2_element
  | TypeBls12_381_MlResult
deriving BEq

mutual
  inductive BuiltinType
    | AtomicType : AtomicType → BuiltinType
    | TypeOperator : TypeOperator → BuiltinType

  inductive TypeOperator
    | TypeList : BuiltinType → TypeOperator
    | TypePair : BuiltinType → BuiltinType → TypeOperator
end

inductive Const
  | Integer               : Integer → Const
  | ByteString            : ByteString → Const
  | String                : String → Const
  | Unit                  : Const
  | Bool                  : Bool → Const
  | ConstList             : List Const → Const
  | ConstDataList         : List Data → Const          -- NOTE: Added to properly implement builtins evaluation and to avoid using List.map
  | ConstPairDataList     : List (Data × Data) → Const -- NOTE: Added to properly implement builtins evaluation and to avoid using List.map
  | Pair                  : Const × Const → Const
  | PairData              : Data × Data → Const        -- NOTE: Added to properly implement builtins evaluation and to avoid using List.map
  | Data                  : Data → Const
  | Bls12_381_G1_element  : BLS12_381_G1_Element → Const
  | Bls12_381_G2_element  : BLS12_381_G2_Element → Const
  | Bls12_381_MlResult    : BLS12_381_MlResult   → Const
deriving Repr


inductive BuiltinFun
-- Batch 1
-- Integer
  | AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger
  | RemainderInteger
  | ModInteger
  | EqualsInteger
  | LessThanInteger
  | LessThanEqualsInteger
-- ByteString
  | AppendByteString
  | ConsByteString
  | SliceByteString
  | LengthOfByteString
  | IndexByteString
  | EqualsByteString
  | LessThanByteString
  | LessThanEqualsByteString
-- Cryptography
  | Sha2_256
  | Sha3_256
  | Blake2b_256
  | VerifyEd25519Signature
-- String
  | AppendString
  | EqualsString
  | EncodeUtf8
  | DecodeUtf8
-- Bool
  | IfThenElse
-- Unit
  | ChooseUnit
-- Tracing
  | Trace
-- Pair
  | FstPair
  | SndPair
-- List
  | ChooseList
  | MkCons
  | HeadList
  | TailList
  | NullList
-- Data
  | ChooseData
  | ConstrData
  | MapData
  | ListData
  | IData
  | BData
  | UnConstrData
  | UnMapData
  | UnListData
  | UnIData
  | UnBData
  | EqualsData
-- Misc constructors
  | MkPairData
  | MkNilData
  | MkNilPairData
-- Batch 2
  | SerializeData
-- Batch 3
  | VerifyEcdsaSecp256k1Signature
  | VerifySchnorrSecp256k1Signature
-- Batch 4 = Chang
-- Bls curve
  | Bls12_381_G1_add
  | Bls12_381_G1_neg
  | Bls12_381_G1_scalarMul
  | Bls12_381_G1_equal
  | Bls12_381_G1_hashToGroup
  | Bls12_381_G1_compress
  | Bls12_381_G1_uncompress
  | Bls12_381_G2_add
  | Bls12_381_G2_neg
  | Bls12_381_G2_scalarMul
  | Bls12_381_G2_equal
  | Bls12_381_G2_hashToGroup
  | Bls12_381_G2_compress
  | Bls12_381_G2_uncompress
  | Bls12_381_G1_multiScalarMul
  | Bls12_381_G2_multiScalarMul
  | Bls12_381_millerLoop
  | Bls12_381_mulMlResult
  | Bls12_381_finalVerify
-- Cryptography
  | Keccak_256
  | Blake2b_224
  | IntegerToByteString
  | ByteStringToInteger

-- Not live yet
-- Batch 5
-- ByteString
  | AndByteString
  | OrByteString
  | XorByteString
  | ComplementByteString
  | ReadBit
  | WriteBits
  | ReplicateByte
  | ShiftByteString
  | RotateByteString
  | CountSetBits
  | FindFirstSetBit
-- Cryptography
  | Ripemd_160
-- Batch 6
  | ExpModInteger
-- Batch 7
  | DropList
deriving Repr, BEq

inductive Term
  | Var : String → Term
  | Const : Const → Term
  | Builtin : BuiltinFun → Term
  | Lam : String → Term → Term
  | Apply : Term → Term → Term
  | Delay : Term → Term
  | Force : Term → Term
  | Constr : Nat → List Term → Term
  | Case : Term → List Term → Term
  | Error : Term
deriving Repr

inductive Version
  | Version : Nat → Nat → Nat → Version

instance : Repr Version where
  reprPrec v _ :=
    "Version " ++ repr v.1 ++ "." ++ repr v.2 ++ "." ++ repr v.3

inductive Program
  | Program : Version → Term → Program
deriving Repr

end PlutusCore.UPLC.Term
