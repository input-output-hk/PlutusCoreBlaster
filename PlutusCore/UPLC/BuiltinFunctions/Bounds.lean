import PlutusCore.ByteString
import PlutusCore.Default

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

Which arguments of which builtin are bounded is recorded with the other argument
types in `argTypes` (`Unlifting.lean`), as `boundedInteger` and
`boundedByteString`.
-/

namespace PlutusCore.UPLC.BuiltinFunctions.Bounds

open PlutusCore.ByteString (ByteString)
open PlutusCore.Default (BuiltinSemanticsVariant)

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

end PlutusCore.UPLC.BuiltinFunctions.Bounds
