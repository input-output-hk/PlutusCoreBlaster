import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.Builtins

open PlutusCore.UPLC.Term
-- Define expectedBuiltinArg
inductive ExpectedBuiltinArg
| ArgV : ExpectedBuiltinArg
| ArgQ : ExpectedBuiltinArg
deriving Repr, BEq

-- Define expectedBuiltinArgs
inductive ExpectedBuiltinArgs
| One : ExpectedBuiltinArg → ExpectedBuiltinArgs
| More : ExpectedBuiltinArg → ExpectedBuiltinArgs → ExpectedBuiltinArgs
deriving Repr, BEq

namespace ExpectedArgNotations

-- Custom notation for `'a' [x]`
syntax "a[" term "]" : term
macro_rules
| `(a[ $x ]) => `(ExpectedBuiltinArgs.One $x)

-- Custom notation for `x ⊙ y`
infixr:99 "⊙" => ExpectedBuiltinArgs.More

end ExpectedArgNotations

open ExpectedArgNotations
open ExpectedBuiltinArgs
open ExpectedBuiltinArg
open BuiltinFun

-- Define expected_args
def expectedArgs (b : BuiltinFun) : ExpectedBuiltinArgs :=
  match b with
  -- Integer
  | AddInteger                      => ArgV ⊙ One ArgV
  | SubtractInteger                 => ArgV ⊙ One ArgV
  | MultiplyInteger                 => ArgV ⊙ One ArgV
  | DivideInteger                   => ArgV ⊙ One ArgV
  | ModInteger                      => ArgV ⊙ One ArgV
  | QuotientInteger                 => ArgV ⊙ One ArgV
  | RemainderInteger                => ArgV ⊙ One ArgV
  | EqualsInteger                   => ArgV ⊙ One ArgV -- added missing entry
  | LessThanInteger                 => ArgV ⊙ One ArgV
  | LessThanEqualsInteger           => ArgV ⊙ One ArgV
  -- ByteString
  | AppendByteString                => ArgV ⊙ One ArgV
  | ConsByteString                  => ArgV ⊙ One ArgV
  | SliceByteString                 => ArgV ⊙ ArgV ⊙ One ArgV
  | LengthOfByteString              => One ArgV
  | IndexByteString                 => ArgV ⊙ One ArgV
  | EqualsByteString                => ArgV ⊙ One ArgV
  | LessThanByteString              => ArgV ⊙ One ArgV
  | LessThanEqualsByteString        => ArgV ⊙ One ArgV
  -- Cryptography
  | Sha2_256                        => One ArgV
  | Sha3_256                        => One ArgV
  | Blake2b_256                     => One ArgV
  | VerifyEd25519Signature          => ArgV ⊙ ArgV ⊙ One ArgV
  | AppendString                    => ArgV ⊙ One ArgV
  | EqualsString                    => ArgV ⊙ One ArgV
  | EncodeUtf8                      => One ArgV
  | DecodeUtf8                      => One ArgV
  | IfThenElse                      => ArgQ ⊙ ArgV ⊙ ArgV ⊙ One ArgV
  | ChooseUnit                      => ArgQ ⊙ ArgV ⊙ One ArgV
  | Trace                           => ArgQ ⊙ ArgV ⊙ One ArgV
  | FstPair                         => ArgQ ⊙ ArgQ ⊙ One ArgV
  | SndPair                         => ArgQ ⊙ ArgQ ⊙ One ArgV
  | ChooseList                      => ArgQ ⊙ ArgQ ⊙ ArgV ⊙ ArgV ⊙ One ArgV
  | MkCons                          => ArgQ ⊙ ArgV ⊙ One ArgV
  | HeadList                        => ArgQ ⊙ One ArgV
  | TailList                        => ArgQ ⊙ One ArgV
  | NullList                        => ArgQ ⊙ One ArgV
  | ChooseData                      => ArgQ ⊙ ArgV ⊙ ArgV ⊙ ArgV ⊙ ArgV ⊙ ArgV ⊙ One ArgV
  | ConstrData                      => ArgV ⊙ One ArgV
  | MapData                         => One ArgV
  | ListData                        => One ArgV
  | IData                           => One ArgV
  | BData                           => One ArgV
  | UnConstrData                    => One ArgV
  | UnMapData                       => One ArgV
  | UnListData                      => One ArgV
  | UnIData                         => One ArgV
  | UnBData                         => One ArgV
  | EqualsData                      => ArgV ⊙ One ArgV
  | MkPairData                      => ArgV ⊙ One ArgV
  | MkNilData                       => One ArgV
  | MkNilPairData                   => One ArgV
  | SerializeData                   => One ArgV
  | VerifyEcdsaSecp256k1Signature   => ArgV ⊙ ArgV ⊙ One ArgV
  | VerifySchnorrSecp256k1Signature => ArgV ⊙ ArgV ⊙ One ArgV
  | Bls12_381_G1_add                => ArgV ⊙ One ArgV
  | Bls12_381_G1_neg                => One ArgV
  | Bls12_381_G1_scalarMul          => ArgV ⊙ One ArgV
  | Bls12_381_G1_equal              => ArgV ⊙ One ArgV
  | Bls12_381_G1_hashToGroup        => ArgV ⊙ One ArgV
  | Bls12_381_G1_compress           => One ArgV
  | Bls12_381_G1_uncompress         => One ArgV
  | Bls12_381_G2_add                => ArgV ⊙ One ArgV
  | Bls12_381_G2_neg                => One ArgV
  | Bls12_381_G2_scalarMul          => ArgV ⊙ One ArgV
  | Bls12_381_G2_equal              => ArgV ⊙ One ArgV
  | Bls12_381_G2_hashToGroup        => ArgV ⊙ One ArgV
  | Bls12_381_G2_compress           => One ArgV
  | Bls12_381_G2_uncompress         => One ArgV
  | Bls12_381_G1_multiScalarMul     => ArgV ⊙ One ArgV
  | Bls12_381_G2_multiScalarMul     => ArgV ⊙ One ArgV
  | Bls12_381_millerLoop            => ArgV ⊙ One ArgV
  | Bls12_381_mulMlResult           => ArgV ⊙ One ArgV
  | Bls12_381_finalVerify           => ArgV ⊙ One ArgV
  | Keccak_256                      => One ArgV
  | Blake2b_224                     => One ArgV
  | IntegerToByteString             => ArgV ⊙ ArgV ⊙ One ArgV
  | ByteStringToInteger             => ArgV ⊙ One ArgV
  -- Batch 5
  | AndByteString                   => ArgV ⊙ ArgV ⊙ One ArgV
  | OrByteString                    => ArgV ⊙ ArgV ⊙ One ArgV
  | XorByteString                   => ArgV ⊙ ArgV ⊙ One ArgV
  | ComplementByteString            => One ArgV
  | ReadBit                         => ArgV ⊙ One ArgV
  | WriteBits                       => ArgV ⊙ ArgV ⊙ One ArgV
  | ReplicateByte                   => ArgV ⊙ One ArgV
  | ShiftByteString                 => ArgV ⊙ One ArgV
  | RotateByteString                => ArgV ⊙ One ArgV
  | CountSetBits                    => One ArgV
  | FindFirstSetBit                 => One ArgV
  | Ripemd_160                      => One ArgV
  -- Batch 6
  | ExpModInteger                   => ArgV ⊙ ArgV ⊙ One ArgV
  -- Batch 7
  | DropList                        => ArgQ ⊙ ArgV ⊙ One ArgV

namespace BuiltinNotations

-- Custom notation for `'α' (b)`
syntax "α(" term ")" : term
macro_rules
| `(α($b)) => `(expectedArgs $b)

end BuiltinNotations

open BuiltinNotations

-- Examples
def example1 := α(BuiltinFun.AddInteger)

end PlutusCore.UPLC.Builtins
