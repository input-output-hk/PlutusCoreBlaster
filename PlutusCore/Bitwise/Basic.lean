import PlutusCore.Integer
import PlutusCore.ByteString.Bytes

namespace PlutusCore.Bitwise
open PlutusCore.Integer
open PlutusCore.Bytes (byteStr uncons takeB dropB repB)

/-! ## Formalisation for PlutusCore Logical and Bitwise builtin functions on ByteString. -/

/- Intead of recreating the Haskell implementation, the design choice was to
   implement the functions in Lean in a way that the observable behavior (responses)
   are the same. This means that successful results are the same and for errors,
   the same error messages are returned in a Left case; the difference is that error
   "traces" are not generated. -/

namespace BitwiseInternal

/-- The maximum length that `integerToByteString` and `replicateByte` can handle. -/
@[simp] def maxOutputLength     : Nat := 8192
@[simp] def maxOutputBitsLength : Nat := 8 * maxOutputLength

/-- Calculates the base-2 logarithm of Integers, returns 0 for negative values. -/
def integerLog2 : Integer → Nat
  | .negSucc _ => 0
  | .ofNat   n => Nat.log2 n

/-- Calculates the "width" of a number in bytes. -/
def integerWidth : Nat → Nat
  | 0 => 0
  | n => Nat.log2 n / 8 + 1

/-- Writes the `p` least significant base-256 digits of `n` onto `a`: in front of it, most
    significant first, if `e` (big-endian); after it, least significant first, otherwise.
    Fails if `n` has more than `p` digits.
    Tail recursive version, uses accumulator for the calculation.
    The bytes come from `byteStr`, so Blaster can translate this for a symbolic `n`. -/
def itobs_loop (e : Bool) : Nat → String → Nat → Except String String
  | .succ p, a, n => itobs_loop e p (if e then byteStr (n % 256) ++ a else a ++ byteStr (n % 256)) (n / 256)
  | .zero  , a, 0 => pure a
  | .zero  , _, _ => throw "integerToByteString: cannot represent Integer in given number of bytes"

/-- Converts a non-negative integer to a bytestring.
    ```
    (e, w, n) → itobs_le (w, n), if e = false
                 itobs_be (w, n), if e = true

    Let 𝑛 = ∑_(𝑖=0)^(𝑁−1) 𝑎_𝑖 * 256 ^ 𝑖
      with 𝑁 ≥ 1, 𝑎_𝑖 ∈ [0..256] for 0 ≤ 𝑖 ≤ 𝑁 − 1 and 𝑎_(𝑁−1) ≠ 0

    itobs_le (𝑤, 𝑛) = itobs_be (w, n) :=
        ×,  if 𝑛 < 0 or 𝑛 ≥ 265536
        ×,  if 𝑤 < 0 or 𝑤 > 8192
        [], if 𝑛 = 0 and 0 ≤ 𝑤 ≤ 8192

    itobs_le (w, n) :=
      [𝑎_0, … , 𝑎_(𝑁−1)], if 𝑤 = 0
      [𝑏_0, … , 𝑏_(𝑤−1)], if 𝑤 > 0 and 𝑁 ≤ 𝑤,
      ×                  , if 𝑤 > 0 and 𝑁 > 𝑤
        where
          b_i := 𝑎_𝑖, if 𝑖 ≤ 𝑁 − 1
                 0  , if 𝑖 ≥ 𝑁

    𝗍𝗈𝖻𝗌_be(𝑤, 𝑛) :=
      [𝑎_(𝑁−1), … , 𝑎_0], if 𝑤 = 0
      [𝑏_0, … , 𝑏_(𝑤−1)], if 𝑤 > 0 and 𝑁 ≤ 𝑤
      ×                  , if 𝑤 > 0 and 𝑁 > 𝑤
        where
          b_i := 0        , if 𝑖 ≤ 𝑤 − 1 − 𝑁
                 𝑎_(𝑤−1−𝑖), if 𝑖 ≥ 𝑤 − 𝑁
    ```
-/
@[simp]
def integerToByteString (e : Bool) (w n : Integer) : Except String String :=
       if w < 0                                       then throw "integerToByteString: negative length argument"
  else if w > maxOutputLength                         then throw s!"integerToByteString: requested length is too long (maximum is {maxOutputLength} bytes)"
  else if w = 0 ∧ integerLog2 n ≥ maxOutputBitsLength then throw s!"integerToByteString: input too long (maximum is 2^{maxOutputBitsLength}-1)"
  else if n < 0                                       then throw "integerToByteString: cannot convert negative Integer"
  else match w, n with
       | 0        , 0         => pure ""
       | 0        , .ofNat n' => itobs_loop e (integerWidth n') "" n'
       | .ofNat w', .ofNat n' => itobs_loop e w'                "" n'
       | _        , _         => unreachable!

/-- Reconstructs a natural number from (at most `n` bytes of) its big-endian representation.
    Tail recursive version, uses accumulator for the calculation.
    Reads bytes with `uncons`, so Blaster can translate this for a symbolic string. -/
def bstoi_be_loop : Nat → String → Nat → Nat
  | 0    , _, acc => acc
  | n + 1, s, acc =>
    match uncons s with
    | none        => acc
    | some (b, t) => bstoi_be_loop n t (acc * 256 + b)

/-- Reconstructs a natural number from (at most `n` bytes of) its little-endian representation.
    Reads bytes with `uncons`, so Blaster can translate this for a symbolic string. -/
def bstoi_le_loop : Nat → String → Nat
  | 0    , _ => 0
  | n + 1, s =>
    match uncons s with
    | none        => 0
    | some (b, t) => b + 256 * bstoi_le_loop n t

/-- The `byteStringToInteger` function converts bytestrings to non-negative integers. -/
def byteStringToInteger (e : Bool) (s : String) : Integer :=
  if e then .ofNat (bstoi_be_loop s.length s 0)
       else .ofNat (bstoi_le_loop s.length s)

/-! ### Bytes as numbers

The builtins below read each byte with `uncons` and write it with `byteStr`, as in
`PlutusCore.Bytes`; no `Char`, `UInt8` or `BitVec` is involved, so Blaster can translate them for
a symbolic string. A byte is a `Nat`, worked on with `+`, `/` and `%` by constants and a `match`
on the bit position, which keeps a solver within linear arithmetic. Every character code `x` is
read as `x % 256`, as `Char.toUInt8` did before, so the builtins agree with their `Char`-based
versions (`Tests.ByteString.Reference`) on every string, not just on byte strings. -/

/-- Bit `i < 8` of the byte `a`, as `0` or `1`. -/
def bitAt (a : Nat) : Nat → Nat
  | 0 => a % 2
  | 1 => a / 2 % 2
  | 2 => a / 4 % 2
  | 3 => a / 8 % 2
  | 4 => a / 16 % 2
  | 5 => a / 32 % 2
  | 6 => a / 64 % 2
  | _ => a / 128 % 2

/-- `2 ^ i`, for `i < 8`. -/
def bitVal : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | _ => 128

/-- The byte `x` shifted left by `r < 8` bits, with the top `r` bits of the next byte `y` shifted
    in: `(x <<< r ||| y >>> (8 - r)) % 256`. -/
def shlByte (r x y : Nat) : Nat :=
  match r with
  | 0 => x
  | 1 => x *   2 % 256 + y / 128
  | 2 => x *   4 % 256 + y /  64
  | 3 => x *   8 % 256 + y /  32
  | 4 => x *  16 % 256 + y /  16
  | 5 => x *  32 % 256 + y /   8
  | 6 => x *  64 % 256 + y /   4
  | _ => x * 128 % 256 + y /   2

/-- The byte `x` shifted right by `r < 8` bits, with the bottom `r` bits of the previous byte `p`
    shifted in: `(p <<< (8 - r) ||| x >>> r) % 256`. -/
def shrByte (r p x : Nat) : Nat :=
  match r with
  | 0 => x
  | 1 => p * 128 % 256 + x /   2
  | 2 => p *  64 % 256 + x /   4
  | 3 => p *  32 % 256 + x /   8
  | 4 => p *  16 % 256 + x /  16
  | 5 => p *   8 % 256 + x /  32
  | 6 => p *   4 % 256 + x /  64
  | _ => p *   2 % 256 + x / 128

/-- The number of set bits in the byte `a`. -/
def popCount (a : Nat) : Nat :=
  a % 2 + a / 2 % 2 + a / 4 % 2 + a / 8 % 2 + a / 16 % 2 + a / 32 % 2 + a / 64 % 2 + a / 128 % 2

/-- The position of the lowest set bit of the byte `a ≠ 0`. -/
def lowestSetBit (a : Nat) : Nat :=
       if a       % 2 = 1 then 0
  else if a /   2 % 2 = 1 then 1
  else if a /   4 % 2 = 1 then 2
  else if a /   8 % 2 = 1 then 3
  else if a /  16 % 2 = 1 then 4
  else if a /  32 % 2 = 1 then 5
  else if a /  64 % 2 = 1 then 6
  else 7

/-- The byte `a` with bit `i < 8` set to `x`. -/
def setBitAt (a i : Nat) (x : Bool) : Nat :=
  if bitAt a i = 1 then (if x then a else a - bitVal i)
                   else (if x then a + bitVal i else a)

/-! ### Logical builtins -/

/-- The bitwise operation of a logical builtin. It is passed as data, not as a function, so that
    the loop over the bytes stays first order for Blaster. -/
inductive LogicOp where
  | and | or | xor

/-- Bitwise `and` of the bytes `a` and `b`: bit `i` of the result is `(x + y) / 2` for bit `x` of
    `a` and bit `y` of `b`. Linear arithmetic, with no case split. -/
def andByte (a b : Nat) : Nat :=
        ((a       % 2 + b       % 2) / 2) +   2 * ((a /   2 % 2 + b /   2 % 2) / 2) +
    4 * ((a /   4 % 2 + b /   4 % 2) / 2) +   8 * ((a /   8 % 2 + b /   8 % 2) / 2) +
   16 * ((a /  16 % 2 + b /  16 % 2) / 2) +  32 * ((a /  32 % 2 + b /  32 % 2) / 2) +
   64 * ((a /  64 % 2 + b /  64 % 2) / 2) + 128 * ((a / 128 % 2 + b / 128 % 2) / 2)

/-- The operation on two bytes. `or` and `xor` follow from `and`, since
    `a + b = (a ^^^ b) + 2 * (a &&& b)` and `a ||| b = (a ^^^ b) + (a &&& b)`. -/
def LogicOp.byte (o : LogicOp) (a b : Nat) : Nat :=
  match o with
  | .and => andByte a b
  | .or  => a + b - andByte a b
  | .xor => a + b - 2 * andByte a b

/-- The byte that the shorter operand is extended with: all ones for `and`, all zeroes otherwise. -/
def LogicOp.pad : LogicOp → Nat
  | .and => 0xFF
  | _    => 0x00

/-- Combines (at most `n` bytes of) `b` and `c` byte by byte with `o`. When one of them runs out
    first, the result ends there unless `e` is true; then the rest of the other one is combined
    with `o.pad`, as if the shorter one had been extended with it. -/
def logicLoop (o : LogicOp) (e : Bool) : Nat → String → String → String
  | 0    , _, _ => ""
  | n + 1, b, c =>
    match uncons b, uncons c with
    | some (x, b'), some (y, c') => byteStr (o.byte (x % 256) (y % 256)) ++ logicLoop o e n b' c'
    | some (x, b'), none         => if e then byteStr (o.byte (x % 256) o.pad) ++ logicLoop o e n b' c else ""
    | none        , some (y, c') => if e then byteStr (o.byte o.pad (y % 256)) ++ logicLoop o e n b c' else ""
    | none        , none         => ""

/-- Extends a bitwise operation to bytestrings. Extends the shorter string if `e` is true,
    otherwise truncates the longer. -/
def logicOp (o : LogicOp) (e : Bool) (b c : String) : String :=
  logicLoop o e (Nat.max b.length c.length) b c

/-- Performs bitwise `and` on bytestrings, extending the lengths if the bool argument is true. -/
def andByteString : Bool → String → String → String := logicOp .and
/-- Performs bitwise `or` on bytestrings, extending the lengths if the bool argument is true. -/
def  orByteString : Bool → String → String → String := logicOp .or
/-- Performs bitwise `xor` on bytestrings, extending the lengths if the bool argument is true. -/
def xorByteString : Bool → String → String → String := logicOp .xor

/-- Complements (at most `n` bytes of) `s`. -/
def complementLoop : Nat → String → String
  | 0    , _ => ""
  | n + 1, s =>
    match uncons s with
    | none        => ""
    | some (x, t) => byteStr (255 - x % 256) ++ complementLoop n t

/-- Performs bitwise complementer calculation on the input bytestring. -/
def complementByteString (b : String) : String := complementLoop b.length b

/-! ### Shifts and rotations

Bits are numbered from the left: shifting or rotating left by `n` moves every bit `n` places
towards the start of the string. The byte strings are traversed a byte at a time: a shift by
`8 * q + r` bits moves whole bytes by `q` places (with `dropB`, `takeB` and `repB`) and bits by
`r` places within a byte, carrying bits over from the neighbouring byte. -/

/-- Shifts (at most `n` bytes of) `s` left by `r < 8` bits. The last byte takes its incoming bits
    from `last`. -/
def shlLoop (r last : Nat) : Nat → String → String
  | 0    , _ => ""
  | n + 1, s =>
    match uncons s with
    | none        => ""
    | some (x, t) =>
      let y := match uncons t with
               | none        => last
               | some (y, _) => y % 256
      byteStr (shlByte r (x % 256) y) ++ shlLoop r last n t

/-- Shifts (at most `n` bytes of) `s` right by `r < 8` bits. The first byte takes its incoming
    bits from `p`. -/
def shrLoop (r : Nat) : Nat → Nat → String → String
  | 0    , _, _ => ""
  | n + 1, p, s =>
    match uncons s with
    | none        => ""
    | some (x, t) => byteStr (shrByte r p (x % 256)) ++ shrLoop r n (x % 256) t

/-- Shifts the bits of `s`
    - `k` places to the left if `k ≥ 0`
    - `k` places to the right if `k < 0` -/
def shiftByteString (s : String) (k : Integer) : String :=
  let len := s.length
  match k with
  | .ofNat n   =>
    if n < 8 * len then shlLoop (n % 8) 0 len (dropB (n / 8) s) ++ repB (n / 8) 0
    else repB len 0
  | .negSucc n =>
    if n + 1 < 8 * len then repB ((n + 1) / 8) 0 ++ shrLoop ((n + 1) % 8) len 0 (takeB (len - (n + 1) / 8) s)
    else repB len 0

/-- Rotates the bits of `s`
    - `k` places to the left if `k ≥ 0`
    - `k` places to the right if `k < 0` -/
def rotateByteString (s : String) (k : Integer) : String :=
  let len   := s.length
  let l     := 8 * len
  -- Rotating right by `m` places is rotating left by `l - m % l` places (`l` places is no rotation).
  let a     := match k with
               | .ofNat n   => n % l
               | .negSucc n => l - (n + 1) % l
  let u     := dropB (a / 8) s ++ takeB (a / 8) s
  let first := match uncons u with
               | none        => 0
               | some (x, _) => x % 256
  shlLoop (a % 8) first len u

/-! ### Counting, reading and writing bits

Bits are indexed from the _right_: bit `8 * j + i` is bit `i` of the `j`-th byte from the end. -/

/-- The number of set bits in (at most `n` bytes of) `s`. -/
def countSetBitsLoop : Nat → String → Nat
  | 0    , _ => 0
  | n + 1, s =>
    match uncons s with
    | none        => 0
    | some (x, t) => popCount (x % 256) + countSetBitsLoop n t

/-- Counts the number of set bits (1) in `s`. -/
def countSetBits (s : String) : Integer := .ofNat (countSetBitsLoop s.length s)

/-- The index, from the right, of the first set bit in (at most `n` bytes of) `s`, or `acc` if
    there is none. Bit `i` of a byte `x` followed by `t` has index `8 * t.length + i`; the last
    byte that is not zero decides. -/
def findFirstSetBitLoop : Nat → String → Integer → Integer
  | 0    , _, acc => acc
  | n + 1, s, acc =>
    match uncons s with
    | none        => acc
    | some (x, t) =>
      findFirstSetBitLoop n t (if x % 256 = 0 then acc else .ofNat (8 * t.length + lowestSetBit (x % 256)))

/-- Finds the index of the first set bit (1) in a bytestring from the _right_.
    Returns -1, if no bits are set. -/
def findFirstSetBit (s : String) : Integer := findFirstSetBitLoop s.length s (-1)

/-- Returns the value of the nth bit in the bytestring.
    Bits are indexed from the _right_. -/
def readBit : String → Integer → Except String Bool
  | _, .negSucc _ => throw "readBit: index out of bounds"
  | s, .ofNat   i =>
      let len := String.length s
      if 8 * len ≤ i then throw "readBit: index out of bounds"
      else
        match uncons (dropB (len - i / 8 - 1) s) with
        | none        => pure false -- unreachable: `i / 8 < len`
        | some (x, _) => pure (bitAt (x % 256) (i % 8) = 1)

/-- Writes the value of the nth bit in the bytestring.
    Bits are indexed from the _right_. -/
def writeBit : String → Integer → Bool → Except String String
  | _, .negSucc _, _ => throw "writeBits: index out of bounds"
  | s, .ofNat   i, x =>
      let len := String.length s
      if 8 * len ≤ i then throw "writeBits: index out of bounds"
      else
        let j := len - i / 8 - 1
        match uncons (dropB j s) with
        | none        => pure s -- unreachable: `i / 8 < len`
        | some (b, t) => pure (takeB j s ++ byteStr (setBitAt (b % 256) (i % 8) x) ++ t)

/-- Writes the value of the list of bits in the bytestring.
    Bits are indexed from the _right_. -/
def writeBits : String → List Integer → Bool → Except String String
  | s, h :: t, x => do writeBits (←writeBit s h x) t x
  | s, []    , _ => pure s

/-- Creates a bytestring by repeating the provided value n times. -/
def replicateByte : Integer → Integer → Except String String
  | .negSucc _, _          => throw "replicateByte: negative length requested"
  | _         , .negSucc _ => throw "replicateByte: negative byte requested"
  | .ofNat   l, .ofNat   b =>
           if maxOutputLength < l then throw s!"replicateByte: requested length is too long (maximum is {maxOutputLength} bytes)"
      else if 255             < b then throw "replicateByte: requested byte is out of range (maximum is 255)"
      else pure (repB l b)

/-- `repr256_le a` returns `n`, if `a` is the little-endian representation of `n`. -/
def repr256_le (a : List Char) : Nat :=
   a |> List.mapIdx (λ i c => (Char.toNat c) * 256 ^ i) |> List.sum

/-- `repr256_be a` returns `n`, if `a` is the big-endian representation of `n`. -/
def repr256_be (a : List Char) : Nat := repr256_le (List.reverse a)

end BitwiseInternal

export BitwiseInternal
  ( -- builtin functions
    integerToByteString
    byteStringToInteger
    andByteString
    orByteString
    xorByteString
    complementByteString
    shiftByteString
    rotateByteString
    countSetBits
    findFirstSetBit
    readBit
    writeBits
    replicateByte
    repr256_le
    repr256_be
  )

end PlutusCore.Bitwise
