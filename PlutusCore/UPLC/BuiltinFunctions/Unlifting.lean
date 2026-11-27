import PlutusCore.Default
import PlutusCore.UPLC.BuiltinFunctions.Bounds
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

/-! # Reading builtin arguments

When a builtin call is saturated, Plutus 1.64 reads ("unlifts") each argument as a
Haskell value of the type the builtin's denotation takes, and only then costs the
call (`toMonoF` in `Builtin/Meaning.hs`). If an argument cannot be read, the call
fails at no cost: `builtinRuntimeFailure` gives it an empty cost. A failure inside
the denotation, after the arguments are read, is charged the builtin's full cost,
e.g. `divideInteger 1 0`, or `headList` on a constant that is not a list.

Reading an argument fails when

- it is not a constant, unless the denotation takes a type variable (`Opaque`),
  which accepts any value;
- the constant has another type, e.g. a `string` for a `bytestring`;
- an integer is outside the range of `Int` [-2^63, 2^63 - 1], `Word8` [0, 255] or
  `Word64` [0, 2^64 - 1] (`readKnownAsInteger` in `Default/Universe.hs`);
- under variants D and E, an argument read as `CInteger` or `CByteString` is out
  of bounds (see `Bounds.lean`).

A polymorphic argument such as `SomeConstant uni [a]` only has to be a constant:
the builtin checks that it is a list itself, so that failure is charged.

`argTypes` records the argument types of every builtin's 1.64 denotation, per
semantics variant. `evaluateBuiltinFunction` runs a builtin only if
`argumentsReadable` holds, and the budgeted machine charges the builtin's cost
only then (`builtinCallCost` in `CekMachine.lean`).

Limitation: a list's element type is part of its type in 1.64, but
`Const.ConstList` does not record it. So an empty `ConstList` is read as a list of
any element type, e.g. as the `[Integer]` of `writeBits`.
-/

namespace PlutusCore.UPLC.BuiltinFunctions.Unlifting

open PlutusCore.Default (BuiltinSemanticsVariant)
open PlutusCore.UPLC.BuiltinFunctions.Bounds
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- The type of a builtin argument in its 1.64 denotation, as far as it decides
    whether the argument can be read. -/
inductive ArgType where
  /-- `Integer`, also `NumBytesCostedAsNumWords` and `IntegerCostedLiterally`. -/
  | integer
  /-- `CInteger` (variants D and E): an integer within `integerBound`. -/
  | boundedInteger
  /-- `Int`: an integer in [-2^63, 2^63 - 1]. -/
  | int
  /-- `Word8`: an integer in [0, 255]. -/
  | word8
  /-- `Word64`: an integer in [0, 2^64 - 1]. -/
  | word64
  | byteString
  /-- `CByteString` (variants D and E): at most `maxByteStringLength` bytes. -/
  | boundedByteString
  /-- `Text`, also `TextCostedByByteLength`. -/
  | string
  | bool
  | unit
  /-- `Data`, also `DataNodeCount`. -/
  | data
  | g1
  | g2
  | mlResult
  /-- `Value`, also `ValueTotalSize` and `ValueMaxDepth`. -/
  | value
  /-- `[Data]` -/
  | dataList
  /-- `[(Data, Data)]` -/
  | dataPairList
  /-- `[Integer]` -/
  | integerList
  /-- `[BLS12_381.G1.Element]` -/
  | g1List
  /-- `[BLS12_381.G2.Element]` -/
  | g2List
  /-- `SomeConstant uni _`: any constant. The builtin checks its shape. -/
  | constant
  /-- A type variable (`Opaque`): any value. -/
  | any
deriving Repr, BEq

/-- Whether constant `c` can be read as an argument of type `t`. -/
def readableConst : ArgType → Const → Bool
  | .integer          , .Integer              _ => true
  | .boundedInteger   , .Integer              x => integerInBounds x
  | .int              , .Integer              x => -9223372036854775808 ≤ x && x ≤ 9223372036854775807
  | .word8            , .Integer              x => 0 ≤ x && x ≤ 255
  | .word64           , .Integer              x => 0 ≤ x && x ≤ 18446744073709551615
  | .byteString       , .ByteString           _ => true
  | .boundedByteString, .ByteString           b => byteStringInBounds b
  | .string           , .String               _ => true
  | .bool             , .Bool                 _ => true
  | .unit             , .Unit                   => true
  | .data             , .Data                 _ => true
  | .g1               , .Bls12_381_G1_element _ => true
  | .g2               , .Bls12_381_G2_element _ => true
  | .mlResult         , .Bls12_381_MlResult   _ => true
  | .value            , .Value                _ => true
  | .dataList         , .ConstDataList        _ => true
  | .dataPairList     , .ConstPairDataList    _ => true
  | .integerList      , .ConstList           xs => xs.all (λ | .Integer              _ => true | _ => false)
  | .g1List           , .ConstList           xs => xs.all (λ | .Bls12_381_G1_element _ => true | _ => false)
  | .g2List           , .ConstList           xs => xs.all (λ | .Bls12_381_G2_element _ => true | _ => false)
  | .constant         , _                       => true
  | .any              , _                       => true
  | _                 , _                       => false

/-- Whether value `V` can be read as an argument of type `t`. -/
def readable : ArgType → CekValue → Bool
  | .any, _       => true
  | t   , .VCon c => readableConst t c
  | _   , _       => false

/-- The argument types of builtin `b` under variant `v`, first argument first,
    following the types of its 1.64 denotation (`toBuiltinMeaning` in
    `Default/Builtins.hs`). -/
def argTypes (v : BuiltinSemanticsVariant) (b : BuiltinFun) : List ArgType :=
  -- `CInteger` and `CByteString` under D and E, `Integer` and `ByteString` otherwise.
  let cInteger    := if ensurable v then ArgType.boundedInteger    else .integer
  let cByteString := if ensurable v then ArgType.boundedByteString else .byteString
  match b with
  -- Integers
  | .AddInteger | .SubtractInteger | .MultiplyInteger | .DivideInteger
  | .QuotientInteger | .RemainderInteger | .ModInteger | .LessThanInteger
  | .LessThanEqualsInteger => [cInteger, cInteger]
  | .EqualsInteger => [.integer, .integer]
  | .ExpModInteger => [.integer, .integer, .integer]
  -- Bytestrings
  | .AppendByteString | .EqualsByteString | .LessThanByteString
  | .LessThanEqualsByteString => [cByteString, cByteString]
  | .ConsByteString =>
      match v with
      | .defaultFunSemanticsVariantA | .defaultFunSemanticsVariantB => [.integer, .byteString]
      | .defaultFunSemanticsVariantC => [.word8, .byteString]
      | .defaultFunSemanticsVariantD => [.boundedInteger, .boundedByteString]
      | .defaultFunSemanticsVariantE => [.word8, .boundedByteString]
  | .SliceByteString => [.int, .int, cByteString]
  | .LengthOfByteString => [.byteString]
  | .IndexByteString => [cByteString, .int]
  -- Hashes and signatures: only the message is bounded.
  | .Sha2_256 | .Sha3_256 | .Blake2b_256 | .Blake2b_224 | .Keccak_256 | .Ripemd_160 =>
      [cByteString]
  | .VerifyEd25519Signature | .VerifySchnorrSecp256k1Signature =>
      [.byteString, cByteString, .byteString]
  | .VerifyEcdsaSecp256k1Signature => [.byteString, .byteString, .byteString]
  -- Strings
  | .AppendString | .EqualsString => [.string, .string]
  | .EncodeUtf8 => [.string]
  | .DecodeUtf8 => [cByteString]
  -- Polymorphic builtins
  | .IfThenElse => [.bool, .any, .any]
  | .ChooseUnit => [.unit, .any]
  | .Trace => [.string, .any]
  | .FstPair | .SndPair => [.constant]
  | .ChooseList => [.constant, .any, .any]
  | .MkCons => [.constant, .constant]
  | .HeadList | .TailList | .NullList => [.constant]
  | .DropList => [.integer, .constant]
  | .LengthOfArray | .ListToArray => [.constant]
  | .IndexArray => [.constant, .int]
  -- Data
  | .ChooseData => [.data, .any, .any, .any, .any, .any]
  | .ConstrData => [if ensurable v then .word64 else .integer, .dataList]
  | .MapData => [.dataPairList]
  | .ListData => [.dataList]
  | .IData => [.integer]
  | .BData => [.byteString]
  | .UnConstrData | .UnMapData | .UnListData | .UnIData | .UnBData | .SerializeData =>
      [.data]
  | .EqualsData | .MkPairData => [.data, .data]
  | .MkNilData | .MkNilPairData => [.unit]
  -- BLS12-381: only the message of `hashToGroup` is bounded, not the tag.
  | .Bls12_381_G1_add | .Bls12_381_G1_equal => [.g1, .g1]
  | .Bls12_381_G1_neg | .Bls12_381_G1_compress => [.g1]
  | .Bls12_381_G1_scalarMul => [.integer, .g1]
  | .Bls12_381_G1_uncompress => [.byteString]
  | .Bls12_381_G1_hashToGroup => [cByteString, .byteString]
  | .Bls12_381_G1_multiScalarMul => [.integerList, .g1List]
  | .Bls12_381_G2_add | .Bls12_381_G2_equal => [.g2, .g2]
  | .Bls12_381_G2_neg | .Bls12_381_G2_compress => [.g2]
  | .Bls12_381_G2_scalarMul => [.integer, .g2]
  | .Bls12_381_G2_uncompress => [.byteString]
  | .Bls12_381_G2_hashToGroup => [cByteString, .byteString]
  | .Bls12_381_G2_multiScalarMul => [.integerList, .g2List]
  | .Bls12_381_millerLoop => [.g1, .g2]
  | .Bls12_381_mulMlResult | .Bls12_381_finalVerify => [.mlResult, .mlResult]
  -- Bitwise
  | .IntegerToByteString => [.bool, .integer, .integer]
  | .ByteStringToInteger => [.bool, cByteString]
  | .AndByteString | .OrByteString | .XorByteString => [.bool, cByteString, cByteString]
  | .ComplementByteString | .CountSetBits | .FindFirstSetBit => [cByteString]
  | .ReadBit => [cByteString, .int]
  | .WriteBits => [.byteString, .integerList, .bool]
  | .ReplicateByte => [.integer, .word8]
  | .ShiftByteString | .RotateByteString =>
      [.byteString, if ensurable v then .int else .integer]
  -- Values
  | .InsertCoin => [.byteString, .byteString, .integer, .value]
  | .LookupCoin => [.byteString, .byteString, .value]
  | .UnionValue | .ValueContains => [.value, .value]
  | .ValueData => [.value]
  | .UnValueData => [.data]
  | .ScaleValue => [.integer, .value]

/-- Whether each value can be read as the argument type at the same position. -/
def allReadable : List ArgType → List CekValue → Bool
  | []     , []      => true
  | t :: ts, V :: Vs => readable t V && allReadable ts Vs
  | _      , _       => false

/-- Whether 1.64 can read the arguments `Vs` of builtin `b` under variant `v`. As
    everywhere in the CEK machine, `Vs` holds the last argument first. -/
def argumentsReadable (v : BuiltinSemanticsVariant) (b : BuiltinFun) (Vs : List CekValue) : Bool :=
  allReadable (argTypes v b).reverse Vs

end PlutusCore.UPLC.BuiltinFunctions.Unlifting
