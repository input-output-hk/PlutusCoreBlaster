import Blaster
import PlutusCore.UPLC

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/84
--
-- Under semantics variants D and E (V1/V2 and V3 from protocol version 11),
-- Plutus 1.64 reads some builtin arguments as `CInteger` or `CByteString`
-- (`Universe/Cardano.hs`). Reading such an argument fails if the integer is
-- outside [-2^262143, 2^262143 - 1] or the bytestring is longer than 65,536
-- bytes. Variants A–C read plain `Integer` and `ByteString` arguments. Results
-- are never bounded.
--
-- Every expected outcome below is what Plutus 1.64.0.0's
-- `uplc evaluate -S <variant>` gives for the same call.
namespace Tests.Issue84

open PlutusCore.Default (BuiltinSemanticsVariant PlutusVersion ProtocolVersion)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.BuiltinFunctions.Evaluate (evaluateBuiltinFunction)
open PlutusCore.UPLC.BuiltinFunctions.Bounds (argumentsInBounds)
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.ExBudget (ExBudget)
open PlutusCore.UPLC.Term (BuiltinFun Const Program Term)
open PlutusCore.UPLC.Utils (isSuccessful)

/-! ## Arguments -/

/-- 2^262143. -/
private def bound : Int := Int.ofNat (2 ^ 262143)

private def maxInteger : Const := .Integer (bound - 1)
private def minInteger : Const := .Integer (-bound)
private def aboveMax   : Const := .Integer bound
private def belowMin   : Const := .Integer (-bound - 1)

/-- `n` bytes `0x61` (`a`), which is also valid UTF-8. -/
private def bytes (n : Nat) : Const := .ByteString ⟨String.mk (List.replicate n 'a')⟩

private def empty : Const := bytes 0
private def maxBytes : Const := bytes 65536
private def tooManyBytes : Const := bytes 65537

private def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

private def hex (s : String) : Const :=
  let rec go : List Char → List Char
    | a :: b :: t => Char.ofNat (16 * hexDigit a + hexDigit b) :: go t
    | _ => []
  .ByteString ⟨String.mk (go s.toList)⟩

-- Valid keys, so that verification runs and returns `False` rather than failing:
-- RFC 8032's first Ed25519 test key and BIP 340's first Schnorr test key.
private def ed25519Key : Const := hex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
private def schnorrKey : Const := hex "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9"
private def signature : Const := hex (String.mk (List.replicate 128 '0'))

/-! ## Calling a builtin under each variant -/

private def variants : List (Char × BuiltinSemanticsVariant) :=
  [ ('A', .defaultFunSemanticsVariantA), ('B', .defaultFunSemanticsVariantB)
  , ('C', .defaultFunSemanticsVariantC), ('D', .defaultFunSemanticsVariantD)
  , ('E', .defaultFunSemanticsVariantE) ]

/-- The arguments as the CEK machine passes them: last argument first. -/
private def stack (args : List Const) : List CekValue := (args.map CekValue.VCon).reverse

/-- The variants, by letter, under which `b` applied to `args` succeeds. -/
private def succeedsUnder (b : BuiltinFun) (args : List Const) : String :=
  String.mk <| variants.filterMap fun (c, v) =>
    if (evaluateBuiltinFunction v b (stack args)).isSome then some c else none

private structure Case where
  name     : String
  builtin  : BuiltinFun
  args     : List Const
  /-- The variants under which the call succeeds. -/
  expected : String

/-- The cases whose outcome differs from the expected one, with the outcome. -/
private def mismatches (cases : List Case) : List String :=
  cases.filterMap fun c =>
    let got := succeedsUnder c.builtin c.args
    if got == c.expected then none else some s!"{c.name}: expected {c.expected}, got {got}"

/-! ## Integer arguments

Both arguments of these builtins are bounded, so each is tested at each end of
the range. -/

private def integerBuiltins : List (String × BuiltinFun) :=
  [ ("addInteger", .AddInteger), ("subtractInteger", .SubtractInteger)
  , ("multiplyInteger", .MultiplyInteger), ("divideInteger", .DivideInteger)
  , ("quotientInteger", .QuotientInteger), ("remainderInteger", .RemainderInteger)
  , ("modInteger", .ModInteger), ("lessThanInteger", .LessThanInteger)
  , ("lessThanEqualsInteger", .LessThanEqualsInteger) ]

private def integerValues : List (String × Const × String) :=
  [ ("2^262143 - 1", maxInteger, "ABCDE"), ("-2^262143", minInteger, "ABCDE")
  , ("2^262143", aboveMax, "ABC"), ("-2^262143 - 1", belowMin, "ABC") ]

private def integerCases : List Case :=
  integerBuiltins.flatMap fun (name, b) => integerValues.flatMap fun (v, x, expected) =>
    [ ⟨s!"{name} ({v}) 1", b, [x, .Integer 1], expected⟩
    , ⟨s!"{name} 1 ({v})", b, [.Integer 1, x], expected⟩ ]

/-- info: [] -/
#guard_msgs in #eval mismatches integerCases

/-! ## Bytestring arguments

Each bounded bytestring argument, at 65,536 and 65,537 bytes. The builtins that
take seconds on 64 KB inputs are tested separately below. -/

private def byteStringCalls : List (String × BuiltinFun × (Const → List Const)) :=
  [ ("appendByteString _ #", .AppendByteString, fun x => [x, empty])
  , ("appendByteString # _", .AppendByteString, fun x => [empty, x])
  , ("consByteString 0 _", .ConsByteString, fun x => [.Integer 0, x])
  , ("sliceByteString 0 1 _", .SliceByteString, fun x => [.Integer 0, .Integer 1, x])
  , ("indexByteString _ 0", .IndexByteString, fun x => [x, .Integer 0])
  , ("equalsByteString _ #", .EqualsByteString, fun x => [x, empty])
  , ("equalsByteString # _", .EqualsByteString, fun x => [empty, x])
  , ("lessThanByteString _ #", .LessThanByteString, fun x => [x, empty])
  , ("lessThanByteString # _", .LessThanByteString, fun x => [empty, x])
  , ("lessThanEqualsByteString _ #", .LessThanEqualsByteString, fun x => [x, empty])
  , ("lessThanEqualsByteString # _", .LessThanEqualsByteString, fun x => [empty, x])
  , ("sha3_256", .Sha3_256, fun x => [x])
  , ("blake2b_256", .Blake2b_256, fun x => [x])
  , ("keccak_256", .Keccak_256, fun x => [x])
  , ("blake2b_224", .Blake2b_224, fun x => [x])
  , ("ripemd_160", .Ripemd_160, fun x => [x])
  -- The message, not the key or the signature.
  , ("verifyEd25519Signature key _ sig", .VerifyEd25519Signature,
      fun x => [ed25519Key, x, signature])
  , ("byteStringToInteger True _", .ByteStringToInteger, fun x => [.Bool true, x])
  , ("andByteString False _ #", .AndByteString, fun x => [.Bool false, x, empty])
  , ("andByteString False # _", .AndByteString, fun x => [.Bool false, empty, x])
  , ("orByteString False _ #", .OrByteString, fun x => [.Bool false, x, empty])
  , ("orByteString False # _", .OrByteString, fun x => [.Bool false, empty, x])
  , ("xorByteString False _ #", .XorByteString, fun x => [.Bool false, x, empty])
  , ("xorByteString False # _", .XorByteString, fun x => [.Bool false, empty, x])
  , ("complementByteString", .ComplementByteString, fun x => [x])
  , ("readBit _ 0", .ReadBit, fun x => [x, .Integer 0]) ]

private def byteStringCases : List Case :=
  byteStringCalls.flatMap fun (name, b, args) =>
    [ ⟨s!"{name} (65536 bytes)", b, args maxBytes, "ABCDE"⟩
    , ⟨s!"{name} (65537 bytes)", b, args tooManyBytes, "ABC"⟩ ]

/-- info: [] -/
#guard_msgs in #eval mismatches byteStringCases

/-! ## Builtins that are slow on 64 KB inputs

On a 65,537-byte input, `sha2_256`, `verifySchnorrSecp256k1Signature`, both
`hashToGroup`s and `decodeUtf8` take about 3 s each, and `countSetBits` and
`findFirstSetBit` about 50 s. So these run only where the bound rejects the call,
which is fast. Where it accepts, the test checks `argumentsInBounds`, the check
`evaluateBuiltinFunction` makes before running the builtin. -/

private def slowCalls : List (String × BuiltinFun × (Const → List Const)) :=
  [ ("sha2_256", .Sha2_256, fun x => [x])
  -- The message, not the key or the signature.
  , ("verifySchnorrSecp256k1Signature key _ sig", .VerifySchnorrSecp256k1Signature,
      fun x => [schnorrKey, x, signature])
  -- The message, not the domain separation tag.
  , ("bls12_381_G1_hashToGroup _ dst", .Bls12_381_G1_hashToGroup, fun x => [x, bytes 3])
  , ("bls12_381_G2_hashToGroup _ dst", .Bls12_381_G2_hashToGroup, fun x => [x, bytes 3])
  , ("decodeUtf8", .DecodeUtf8, fun x => [x])
  , ("countSetBits", .CountSetBits, fun x => [x])
  , ("findFirstSetBit", .FindFirstSetBit, fun x => [x]) ]

/-- The variants, by letter, under which `argumentsInBounds` accepts the call. -/
private def inBoundsUnder (b : BuiltinFun) (args : List Const) : String :=
  String.mk <| variants.filterMap fun (c, v) =>
    if argumentsInBounds v b (stack args) then some c else none

/-- info: [] -/
#guard_msgs in #eval slowCalls.filterMap fun (name, b, args) =>
  let rejected := [BuiltinSemanticsVariant.defaultFunSemanticsVariantD, .defaultFunSemanticsVariantE].all
    fun v => (evaluateBuiltinFunction v b (stack (args tooManyBytes))).isNone
  let accepted := (inBoundsUnder b (args maxBytes), inBoundsUnder b (args tooManyBytes))
  if rejected && accepted == ("ABCDE", "ABC") then none
  else some s!"{name}: rejected under D/E: {rejected}, in bounds: {accepted}"

/-! ## Arguments and results that are not bounded -/

private def unboundedCases : List Case :=
  [ -- `equalsInteger` reads plain `Integer`s in every variant.
    ⟨"equalsInteger (2^262143) 1", .EqualsInteger, [aboveMax, .Integer 1], "ABCDE"⟩
  , ⟨"equalsInteger 1 (-2^262143 - 1)", .EqualsInteger, [.Integer 1, belowMin], "ABCDE"⟩
  , ⟨"iData (2^262143)", .IData, [aboveMax], "ABCDE"⟩
  , ⟨"lengthOfByteString (65537 bytes)", .LengthOfByteString, [tooManyBytes], "ABCDE"⟩
  , ⟨"bData (65537 bytes)", .BData, [tooManyBytes], "ABCDE"⟩
    -- Results may exceed the bounds.
  , ⟨"multiplyInteger (2^262143 - 1) (2^262143 - 1)", .MultiplyInteger,
      [maxInteger, maxInteger], "ABCDE"⟩
  , ⟨"appendByteString (65536 bytes) (65536 bytes)", .AppendByteString,
      [maxBytes, maxBytes], "ABCDE"⟩
    -- `consByteString`'s integer is a `CInteger` under D, reduced modulo 256,
    -- and a `Word8` under C and E, which rejects anything outside [0, 255].
  , ⟨"consByteString (2^262143 - 1) #", .ConsByteString, [maxInteger, empty], "ABD"⟩
  , ⟨"consByteString (-2^262143) #", .ConsByteString, [minInteger, empty], "ABD"⟩
  , ⟨"consByteString (2^262143) #", .ConsByteString, [aboveMax, empty], "AB"⟩
  , ⟨"consByteString (-2^262143 - 1) #", .ConsByteString, [belowMin, empty], "AB"⟩
  , ⟨"consByteString 256 #", .ConsByteString, [.Integer 256, empty], "ABD"⟩ ]

/-- info: [] -/
#guard_msgs in #eval mismatches unboundedCases

/-! ## Through the CEK machine -/

private def program (t : Term) : Program := .Program (.Version 1 1 0) t

/-- `[(builtin addInteger) (con integer x) (con integer 1)]` -/
private def addOne (x : Int) : Program :=
  program (.Apply (.Apply (.Builtin .AddInteger) (.Const (.Integer x))) (.Const (.Integer 1)))

/-- `[(builtin sha3_256) (con bytestring b)]` -/
private def sha3 (b : Const) : Program := program (.Apply (.Builtin .Sha3_256) (.Const b))

private def halts : State → Bool
  | .Halt _ => true
  | _ => false

private def errors : State → Bool
  | .Error => true
  | _ => false

-- `cekExecuteProgram` runs variant E.
#guard halts (cekExecuteProgram (addOne (bound - 1)) [] 20)
#guard errors (cekExecuteProgram (addOne bound) [] 20)
#guard halts (cekExecuteProgram (sha3 maxBytes) [] 20)
#guard errors (cekExecuteProgram (sha3 tooManyBytes) [] 20)

private def budget : ExBudget := ⟨⟨10_000_000_000⟩, ⟨100_000_000⟩⟩

private def succeeds : EvaluationResult → Bool
  | .Success .. => true
  | _ => false

private def fails : EvaluationResult → Bool
  | .EvaluationError => true
  | _ => false

-- At the default (current mainnet) protocol version, V1/V2 run variant D and V3
-- runs E. At `.preConway`, V1/V2 run A and V3 runs C.
--
-- Only bytestrings here: costing an integer near 2^262143 does not finish,
-- because `costingLog2` recurses once per bit.
#guard fails (cekExecuteProgramWithBudget (sha3 tooManyBytes) .plutusV1 default [] budget)
#guard fails (cekExecuteProgramWithBudget (sha3 tooManyBytes) .plutusV3 default [] budget)
#guard succeeds (cekExecuteProgramWithBudget (sha3 maxBytes) .plutusV3 default [] budget)
#guard succeeds (cekExecuteProgramWithBudget (sha3 tooManyBytes) .plutusV1 .preConway [] budget)
#guard succeeds (cekExecuteProgramWithBudget (sha3 tooManyBytes) .plutusV3 .preConway [] budget)

/-! ## Evaluation in proofs

`Bounds.integerBound` is `2 ^ 262143`. The elaborator does not evaluate powers
with an exponent above `exponentiation.threshold`, so `decide` and `rfl` on a
bounded integer argument need the option. The kernel needs nothing. -/

set_option exponentiation.threshold 262143 in
example : evaluateBuiltinFunction .defaultFunSemanticsVariantE .AddInteger
    (stack [.Integer 1, .Integer 2]) = some (.VCon (.Integer 3)) := by decide

example : evaluateBuiltinFunction .defaultFunSemanticsVariantE .AddInteger
    (stack [.Integer 1, .Integer 2]) = some (.VCon (.Integer 3)) := by decide +kernel

/-! ## Symbolic arguments

Under E the bounds are a precondition of success, and Blaster can use them. -/

example : ∀ x : Int, -bound ≤ x → x < bound →
  cekExecuteProgram (addOne x) [] 20 = .Halt (.VCon (.Integer (x + 1))) :=
    by blaster

example : ∀ x : Int, x < -bound ∨ bound ≤ x → cekExecuteProgram (addOne x) [] 20 = .Error :=
  by blaster

example : ∀ b : ByteString, b.length ≤ 65536 →
  isSuccessful (cekExecuteProgram (sha3 (.ByteString b)) [] 20) :=
    by blaster

example : ∀ b : ByteString, 65536 < b.length →
  cekExecuteProgram (sha3 (.ByteString b)) [] 20 = .Error :=
    by blaster

end Tests.Issue84
