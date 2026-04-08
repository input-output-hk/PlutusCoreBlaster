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
def evaluateBuiltinFunction (semanticsVariant : BuiltinSemanticsVariant) (b : BuiltinFun) : List CekValue → Option CekValue :=
  match b with
  -- Batch 1
  -- Integer
  | .AddInteger                      => addInteger
  | .SubtractInteger                 => subtractInteger
  | .MultiplyInteger                 => multiplyInteger
  | .DivideInteger                   => divideInteger
  | .QuotientInteger                 => quotientInteger
  | .RemainderInteger                => remainderInteger
  | .ModInteger                      => modInteger
  | .EqualsInteger                   => equalsInteger
  | .LessThanInteger                 => lessThanInteger
  | .LessThanEqualsInteger           => lessThanEqualsInteger
  -- ByteString
  | .AppendByteString                => appendByteString
  | .ConsByteString                  => consByteString semanticsVariant
  | .SliceByteString                 => sliceByteString
  | .LengthOfByteString              => lengthOfByteString
  | .IndexByteString                 => indexByteString
  | .EqualsByteString                => equalsByteString
  | .LessThanByteString              => lessThanByteString
  | .LessThanEqualsByteString        => lessThanEqualsByteString
  -- Cryptography
  | .Sha2_256                        => Crypto.sha2_256
  | .Sha3_256                        => Crypto.sha3_256
  | .Blake2b_256                     => Crypto.blake2b_256
  | .VerifyEd25519Signature          => Crypto.verifyEd25519Signature
  -- String
  | .AppendString                    => appendString
  | .EqualsString                    => equalsString
  | .EncodeUtf8                      => encodeUtf8
  | .DecodeUtf8                      => decodeUtf8
  -- Bool
  | .IfThenElse                      => ifThenElse
  -- Unit
  | .ChooseUnit                      => chooseUnit
  -- Tracing
  | .Trace                           => trace
  -- Pair
  | .FstPair                         => fstPair
  | .SndPair                         => sndPair
  -- List
  | .ChooseList                      => chooseList
  | .MkCons                          => mkCons
  | .HeadList                        => headList
  | .TailList                        => tailList
  | .NullList                        => nullList
  -- Data
  | .ChooseData                      => chooseData
  | .ConstrData                      => constrData
  | .MapData                         => mapData
  | .ListData                        => listData
  | .IData                           => iData
  | .BData                           => bData
  | .UnConstrData                    => unConstrData
  | .UnMapData                       => unMapData
  | .UnListData                      => unListData
  | .UnIData                         => unIData
  | .UnBData                         => unBData
  | .EqualsData                      => equalsData
  -- Misc constructors
  | .MkPairData                      => mkPairData
  | .MkNilData                       => mkNilData
  | .MkNilPairData                   => mkNilPairData
  -- Batch 2
  | .SerializeData                   => serializeData
  -- Batch 3
  | .VerifyEcdsaSecp256k1Signature   => Crypto.verifyEcdsaSecp256k1Signature
  | .VerifySchnorrSecp256k1Signature => Crypto.verifySchnorrSecp256k1Signature
  -- Batch 4
  -- BLS curve
  | .Bls12_381_G1_add                => Crypto.bls12381G1Add
  | .Bls12_381_G1_neg                => Crypto.bls12381G1Neg
  | .Bls12_381_G1_scalarMul          => Crypto.bls12381G1ScalarMul
  | .Bls12_381_G1_equal              => Crypto.bls12381G1Equal
  | .Bls12_381_G1_hashToGroup        => Crypto.bls12381G1HashToGroup
  | .Bls12_381_G1_compress           => Crypto.bls12381G1Compress
  | .Bls12_381_G1_uncompress         => Crypto.bls12381G1Uncompress
  | .Bls12_381_G2_add                => Crypto.bls12381G2Add
  | .Bls12_381_G2_neg                => Crypto.bls12381G2Neg
  | .Bls12_381_G2_scalarMul          => Crypto.bls12381G2ScalarMul
  | .Bls12_381_G2_equal              => Crypto.bls12381G2Equal
  | .Bls12_381_G2_hashToGroup        => Crypto.bls12381G2HashToGroup
  | .Bls12_381_G2_compress           => Crypto.bls12381G2Compress
  | .Bls12_381_G2_uncompress         => Crypto.bls12381G2Uncompress
  | .Bls12_381_G1_multiScalarMul     => Crypto.bls12381G1MultiScalarMul
  | .Bls12_381_G2_multiScalarMul     => Crypto.bls12381G2MultiScalarMul
  | .Bls12_381_millerLoop            => Crypto.bls12381MillerLoop
  | .Bls12_381_mulMlResult           => Crypto.bls12381MulMlResult
  | .Bls12_381_finalVerify           => Crypto.bls12381FinalVerify
  -- Other cryptography
  | .Keccak_256                      => Crypto.keccak_256
  | .Blake2b_224                     => Crypto.blake2b_224
  | .IntegerToByteString             => Bitwise.integerToByteString
  | .ByteStringToInteger             => Bitwise.byteStringToInteger
  -- Batch 5
  -- ByteString
  | .AndByteString                   => Bitwise.andByteString
  | .OrByteString                    => Bitwise.orByteString
  | .XorByteString                   => Bitwise.xorByteString
  | .ComplementByteString            => Bitwise.complementByteString
  | .ReadBit                         => Bitwise.readBit
  | .WriteBits                       => Bitwise.writeBits
  | .ReplicateByte                   => Bitwise.replicateByte
  | .ShiftByteString                 => Bitwise.shiftByteString
  | .RotateByteString                => Bitwise.rotateByteString
  | .CountSetBits                    => Bitwise.countSetBits
  | .FindFirstSetBit                 => Bitwise.findFirstSetBit
  -- Cryptography
  | .Ripemd_160                      => Crypto.ripemd_160
  -- Batch 6
  | .ExpModInteger                   => expModInteger
  -- Batch 7
  | .DropList                        => dropList

end PlutusCore.UPLC.BuiltinFunctions.Evaluate
