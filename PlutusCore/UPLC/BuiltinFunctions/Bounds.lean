import PlutusCore.ByteString
import PlutusCore.Default
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term

/-! # Builtin argument bounds under semantics variants D and E

Under variants D and E, which the ledger uses for V1/V2 and V3 from protocol
version 11, Plutus 1.64 reads some builtin arguments as `CInteger` or
`CByteString` instead of `Integer` or `ByteString` (`ensurable` in
`Default/Builtins.hs`). Reading such an argument fails when

- the integer is outside [-2^262143, 2^262143 - 1] ("Integer out of bounds"), or
- the bytestring is longer than 65,536 bytes ("ByteString overflow"),

see the `CInteger` and `CByteString` readers in `Default/Universe.hs` and the
constants in `Default/Universe/Cardano.hs`. The failure is an ordinary
evaluation failure, and it happens before the builtin runs. Only arguments are
bounded: results such as `multiplyInteger`'s or `appendByteString`'s may exceed
the bounds. Variants A–C bound nothing.

`argumentsInBounds` lists the bounded arguments of each builtin, following the
types of their 1.64 denotations. `evaluateBuiltinFunction` runs a builtin only
if it returns `true`.
-/

namespace PlutusCore.UPLC.BuiltinFunctions.Bounds

open PlutusCore.ByteString (ByteString)
open PlutusCore.Default (BuiltinSemanticsVariant)
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- Whether a semantics variant bounds builtin arguments (`ensurable` in 1.64's
    `Builtins.hs`). -/
def ensurable : BuiltinSemanticsVariant → Bool
  | .defaultFunSemanticsVariantD | .defaultFunSemanticsVariantE => true
  | _ => false

/-- 2^262143. An integer argument read as `CInteger` must lie in
    [-integerBound, integerBound - 1] (`minBoundInteger` and `maxBoundInteger`
    in `Universe/Cardano.hs`).

    It is a `Nat.pow` because Blaster folds `Nat.pow` of two literals into a
    literal; it cannot unfold the equivalent `1 <<< 262143`. Lean's elaborator
    does not evaluate a power whose exponent exceeds `exponentiation.threshold`
    (256 by default), so `decide` and `rfl` on a call with a bounded integer
    argument need `set_option exponentiation.threshold 262143`. The kernel
    evaluates it without that option, e.g. in `decide +kernel`. -/
def integerBound : Int := Int.ofNat (2 ^ 262143)

/-- Whether `x` can be read as a `CInteger`, i.e.
    `-integerBound ≤ x ∧ x < integerBound`.

    Written with a single comparison against `integerBound`: Blaster prints each
    occurrence of its 78,913-digit literal into the SMT query, which takes
    about 1.7 s. -/
def integerInBounds (x : Int) : Bool :=
  (if x < 0 then -x - 1 else x) < integerBound

/-- An argument read as `CByteString` has at most this many bytes
    (`maxBoundByteString` in `Universe/Cardano.hs`). -/
def maxByteStringLength : Nat := 65536

/-- Whether `b` can be read as a `CByteString`. -/
def byteStringInBounds (b : ByteString) : Bool :=
  b.length ≤ maxByteStringLength

/-- Whether an argument read as `CInteger` is within bounds. An argument of
    another type is left to the builtin, which fails on it. -/
def integerArg : CekValue → Bool
  | .VCon (.Integer x) => integerInBounds x
  | _ => true

/-- Whether an argument read as `CByteString` is within bounds. An argument of
    another type is left to the builtin, which fails on it. -/
def byteStringArg : CekValue → Bool
  | .VCon (.ByteString b) => byteStringInBounds b
  | _ => true

/-- Whether the arguments `Vs` of builtin `b` are within the bounds of semantics
    variant `v`. As everywhere in the CEK machine, `Vs` holds the last argument
    first. Each comment gives the argument types of the 1.64 denotation, where
    `_` is a type that is not bounded. -/
def argumentsInBounds (v : BuiltinSemanticsVariant) (b : BuiltinFun) (Vs : List CekValue) : Bool :=
  !ensurable v ||
  match b with
  -- `CInteger → CInteger`
  | .AddInteger | .SubtractInteger | .MultiplyInteger | .DivideInteger
  | .QuotientInteger | .RemainderInteger | .ModInteger | .LessThanInteger
  | .LessThanEqualsInteger =>
      match Vs with
      | [y, x] => integerArg x && integerArg y
      | _ => true
  -- `CByteString → CByteString`
  | .AppendByteString | .EqualsByteString | .LessThanByteString
  | .LessThanEqualsByteString =>
      match Vs with
      | [y, x] => byteStringArg x && byteStringArg y
      | _ => true
  -- `CByteString`
  | .Sha2_256 | .Sha3_256 | .Blake2b_256 | .Blake2b_224 | .Keccak_256 | .Ripemd_160
  | .ComplementByteString | .CountSetBits | .FindFirstSetBit | .DecodeUtf8 =>
      match Vs with
      | [x] => byteStringArg x
      | _ => true
  -- `CByteString → _`: the index of `indexByteString` and `readBit` is an
  -- `Int`; the domain separation tag of `hashToGroup` is not bounded.
  | .IndexByteString | .ReadBit | .Bls12_381_G1_hashToGroup | .Bls12_381_G2_hashToGroup =>
      match Vs with
      | [_, x] => byteStringArg x
      | _ => true
  -- `_ → CByteString`: the flag of `byteStringToInteger` is a `Bool`.
  | .ByteStringToInteger =>
      match Vs with
      | [x, _] => byteStringArg x
      | _ => true
  -- `CInteger → CByteString` under D, then reduced modulo 256;
  -- `Word8 → CByteString` under E, where `consByteStringV2` rejects the integer
  -- outside [0, 255] anyway.
  | .ConsByteString =>
      match Vs with
      | [x, n] =>
          byteStringArg x &&
          match v with
          | .defaultFunSemanticsVariantD => integerArg n
          | _ => true
      | _ => true
  -- `Int → Int → CByteString`
  | .SliceByteString =>
      match Vs with
      | [x, _, _] => byteStringArg x
      | _ => true
  -- `_ → CByteString → CByteString`: the flag is a `Bool`.
  | .AndByteString | .OrByteString | .XorByteString =>
      match Vs with
      | [y, x, _] => byteStringArg x && byteStringArg y
      | _ => true
  -- `_ → CByteString → _`: only the message; the key and the signature are not
  -- bounded.
  | .VerifyEd25519Signature | .VerifySchnorrSecp256k1Signature =>
      match Vs with
      | [_, msg, _] => byteStringArg msg
      | _ => true
  | _ => true

end PlutusCore.UPLC.BuiltinFunctions.Bounds
