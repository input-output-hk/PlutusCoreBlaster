import PlutusCore.Default
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Array
import PlutusCore.UPLC.BuiltinFunctions.Bool
import PlutusCore.UPLC.BuiltinFunctions.ByteString
import PlutusCore.UPLC.BuiltinFunctions.Data
import PlutusCore.UPLC.BuiltinFunctions.Integer
import PlutusCore.UPLC.BuiltinFunctions.List
import PlutusCore.UPLC.BuiltinFunctions.Pair
import PlutusCore.UPLC.BuiltinFunctions.String
import PlutusCore.UPLC.BuiltinFunctions.Trace
import PlutusCore.UPLC.BuiltinFunctions.Unit


namespace PlutusCore.UPLC.Evaluate
open PlutusCore.Default
open PlutusCore.UPLC.Array
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue

-- Evaluate a builtin function based on its type.
def evaluateBuiltinFunction (semanticsVariant : BuiltinSemanticsVariant) (b : BuiltinFun) : List CekValue → Option CekValue :=
  match b with
  | .AddInteger => addInteger
  | .SubtractInteger => subtractInteger
  | .MultiplyInteger => multiplyInteger
  | .DivideInteger => divideInteger
  | .QuotientInteger => quotientInteger
  | .RemainderInteger => remainderInteger
  | .ModInteger => modInteger
  | .EqualsInteger => equalsInteger
  | .LessThanInteger => lessThanInteger
  | .LessThanEqualsInteger => lessThanEqualsInteger
  | .AppendByteString => appendByteString
  | .ConsByteString => consByteString semanticsVariant
  | .SliceByteString => sliceByteString
  | .LengthOfByteString => lengthOfByteString
  | .IndexByteString => indexByteString
  | .EqualsByteString => equalsByteString
  | .LessThanByteString => lessThanByteString
  | .LessThanEqualsByteString => lessThanEqualsByteString
  | .AppendString => appendString
  | .EqualsString => equalsString
  | .EncodeUtf8 => encodeUtf8
  | .DecodeUtf8 => decodeUtf8
  | .IfThenElse => ifThenElse
  | .ChooseUnit => chooseUnit
  | .Trace => trace
  | .FstPair => fstPair
  | .SndPair => sndPair
  | .ChooseList => chooseList
  | .MkCons => mkCons
  | .HeadList => headList
  | .TailList => tailList
  | .NullList => nullList
  | .ChooseData => chooseData
  | .ConstrData => constrData
  | .MapData => mapData
  | .ListData => listData
  | .IData => iData
  | .BData => bData
  | .UnConstrData => unConstrData
  | .UnMapData => unMapData
  | .UnListData => unListData
  | .UnIData => unIData
  | .UnBData => unBData
  | .EqualsData => equalsData
  | .MkPairData => mkPairData
  | .MkNilData => mkNilData
  | .MkNilPairData => mkNilPairData
  | .LengthOfArray => lengthOfArray
  | .ListToArray => listToArray
  | .IndexArray => indexArray
  | _ => fun _ => none

end PlutusCore.UPLC.Evaluate
