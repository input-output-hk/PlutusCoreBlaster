import PlutusCore.Default
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Bitwise
import PlutusCore.UPLC.BuiltinFunctions.Bool
import PlutusCore.UPLC.BuiltinFunctions.ByteString
import PlutusCore.UPLC.BuiltinFunctions.Crypto
import PlutusCore.UPLC.BuiltinFunctions.Data
import PlutusCore.UPLC.BuiltinFunctions.Integer
import PlutusCore.UPLC.BuiltinFunctions.List
import PlutusCore.UPLC.BuiltinFunctions.Pair
import PlutusCore.UPLC.BuiltinFunctions.String
import PlutusCore.UPLC.BuiltinFunctions.Trace
import PlutusCore.UPLC.BuiltinFunctions.Unit

namespace PlutusCore.UPLC.BuiltinFunctions.Evaluate

open PlutusCore.Default
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.BuiltinFunctions.Bitwise
open PlutusCore.UPLC.BuiltinFunctions.Bool
open PlutusCore.UPLC.BuiltinFunctions.ByteString
open PlutusCore.UPLC.BuiltinFunctions.Data
open PlutusCore.UPLC.BuiltinFunctions.Integer
open PlutusCore.UPLC.BuiltinFunctions.List
open PlutusCore.UPLC.BuiltinFunctions.Pair
open PlutusCore.UPLC.BuiltinFunctions.String
open PlutusCore.UPLC.BuiltinFunctions.Trace
open PlutusCore.UPLC.BuiltinFunctions.Unit

-- Evaluate a builtin function based on its type.
def evaluateBuiltinFunction (semanticsVariant : BuiltinSemanticsVariant) (b : BuiltinFun) (Vs : List CekValue) : Option CekValue :=
  match b with
  -- Batch 1
  -- Integer
  | .AddInteger                      => addInteger Vs
  | .SubtractInteger                 => subtractInteger Vs
  | .MultiplyInteger                 => multiplyInteger Vs
  | .DivideInteger                   => divideInteger Vs
  | .QuotientInteger                 => quotientInteger Vs
  | .RemainderInteger                => remainderInteger Vs
  | .ModInteger                      => modInteger Vs
  | .EqualsInteger                   => equalsInteger Vs
  | .LessThanInteger                 => lessThanInteger Vs
  | .LessThanEqualsInteger           => lessThanEqualsInteger Vs
  -- ByteString
  | .AppendByteString                => appendByteString Vs
  | .ConsByteString                  => consByteString semanticsVariant Vs
  | .SliceByteString                 => sliceByteString Vs
  | .LengthOfByteString              => lengthOfByteString Vs
  | .IndexByteString                 => indexByteString Vs
  | .EqualsByteString                => equalsByteString Vs
  | .LessThanByteString              => lessThanByteString Vs
  | .LessThanEqualsByteString        => lessThanEqualsByteString Vs
  -- Cryptography
  | .Sha2_256                        => Crypto.sha2_256 Vs
  | .Sha3_256                        => Crypto.sha3_256 Vs
  | .Blake2b_256                     => Crypto.blake2b_256 Vs
  | .VerifyEd25519Signature          => Crypto.verifyEd25519Signature Vs
  -- String
  | .AppendString                    => appendString Vs
  | .EqualsString                    => equalsString Vs
  | .EncodeUtf8                      => encodeUtf8 Vs
  | .DecodeUtf8                      => decodeUtf8 Vs
  -- Bool
  | .IfThenElse                      => ifThenElse Vs
  -- Unit
  | .ChooseUnit                      => chooseUnit Vs
  -- Tracing
  | .Trace                           => trace Vs
  -- Pair
  | .FstPair                         => fstPair Vs
  | .SndPair                         => sndPair Vs
  -- List
  | .ChooseList                      => chooseList Vs
  | .MkCons                          => mkCons Vs
  | .HeadList                        => headList Vs
  | .TailList                        => tailList Vs
  | .NullList                        => nullList Vs
  -- Data
  | .ChooseData                      => chooseData Vs
  | .ConstrData                      => constrData Vs
  | .MapData                         => mapData Vs
  | .ListData                        => listData Vs
  | .IData                           => iData Vs
  | .BData                           => bData Vs
  | .UnConstrData                    => unConstrData Vs
  | .UnMapData                       => unMapData Vs
  | .UnListData                      => unListData Vs
  | .UnIData                         => unIData Vs
  | .UnBData                         => unBData Vs
  | .EqualsData                      => equalsData Vs
  -- Misc constructors
  | .MkPairData                      => mkPairData Vs
  | .MkNilData                       => mkNilData Vs
  | .MkNilPairData                   => mkNilPairData Vs
  -- Batch 2
  | .SerializeData                   => serializeData Vs
  -- Batch 3
  | .VerifyEcdsaSecp256k1Signature   => Crypto.verifyEcdsaSecp256k1Signature Vs
  | .VerifySchnorrSecp256k1Signature => Crypto.verifySchnorrSecp256k1Signature Vs
  -- Batch 4
  -- BLS curve
  | .Bls12_381_G1_add                => Crypto.bls12381G1Add Vs
  | .Bls12_381_G1_neg                => Crypto.bls12381G1Neg Vs
  | .Bls12_381_G1_scalarMul          => Crypto.bls12381G1ScalarMul Vs
  | .Bls12_381_G1_equal              => Crypto.bls12381G1Equal Vs
  | .Bls12_381_G1_hashToGroup        => Crypto.bls12381G1HashToGroup Vs
  | .Bls12_381_G1_compress           => Crypto.bls12381G1Compress Vs
  | .Bls12_381_G1_uncompress         => Crypto.bls12381G1Uncompress Vs
  | .Bls12_381_G2_add                => Crypto.bls12381G2Add Vs
  | .Bls12_381_G2_neg                => Crypto.bls12381G2Neg Vs
  | .Bls12_381_G2_scalarMul          => Crypto.bls12381G2ScalarMul Vs
  | .Bls12_381_G2_equal              => Crypto.bls12381G2Equal Vs
  | .Bls12_381_G2_hashToGroup        => Crypto.bls12381G2HashToGroup Vs
  | .Bls12_381_G2_compress           => Crypto.bls12381G2Compress Vs
  | .Bls12_381_G2_uncompress         => Crypto.bls12381G2Uncompress Vs
  | .Bls12_381_G1_multiScalarMul     => Crypto.bls12381G1MultiScalarMul Vs
  | .Bls12_381_G2_multiScalarMul     => Crypto.bls12381G2MultiScalarMul Vs
  | .Bls12_381_millerLoop            => Crypto.bls12381MillerLoop Vs
  | .Bls12_381_mulMlResult           => Crypto.bls12381MulMlResult Vs
  | .Bls12_381_finalVerify           => Crypto.bls12381FinalVerify Vs
  -- Other cryptography
  | .Keccak_256                      => Crypto.keccak_256 Vs
  | .Blake2b_224                     => Crypto.blake2b_224 Vs
  -- Batch 5 (bitwise)
  | .IntegerToByteString             => integerToByteString Vs
  | .ByteStringToInteger             => byteStringToInteger Vs
  | .AndByteString                   => andByteString Vs
  | .OrByteString                    => orByteString Vs
  | .XorByteString                   => xorByteString Vs
  | .ComplementByteString            => complementByteString Vs
  | .ReadBit                         => readBit Vs
  | .WriteBits                       => writeBits Vs
  | .ReplicateByte                   => replicateByte Vs
  | .ShiftByteString                 => shiftByteString Vs
  | .RotateByteString                => rotateByteString Vs
  | .CountSetBits                    => countSetBits Vs
  | .FindFirstSetBit                 => findFirstSetBit Vs
  -- Cryptography
  | .Ripemd_160                      => Crypto.ripemd_160 Vs
  -- Batch 6
  | .ExpModInteger                   => expModInteger Vs
  -- Batch 7
  | .DropList                        => dropList Vs

end PlutusCore.UPLC.BuiltinFunctions.Evaluate
