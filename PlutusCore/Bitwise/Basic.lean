import PlutusCore.Integer

namespace PlutusCore.Bitwise
open PlutusCore.Integer

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

/-- Calculates the big-endian representation of a natural number with maximal byte width.
    Tail recursive version, uses accumulator for the calculation. -/
def itobs_be_loop : Nat → List Char → Nat → Except String (List Char)
  | .succ p, a, n => itobs_be_loop p (Char.ofNat (n % 256) :: a) (n / 256)
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
  else do
    let r ← match w, n with
             | 0        , 0         => pure []
             | 0        , .ofNat n' => itobs_be_loop (integerWidth n') [] n'
             | .ofNat w', .ofNat n' => itobs_be_loop w'                [] n'
             | _        , _         => unreachable!
    if e then pure ⟨r⟩
         else pure ⟨r.reverse⟩

/-- Reconstructs a natural number from it's big-endian representation.
    Tail recursive version, uses accumulator for the calculation. -/
def bstoi_be_loop : List Char → Nat → Nat
  | []    , acc => acc
  | h :: t, acc => bstoi_be_loop t (acc * 256 + (Char.toNat h))

/-- The `byteStringToInteger` function converts bytestrings to non-negative integers. -/
def byteStringToInteger (e : Bool) (s : String) : Integer :=
  if e then .ofNat (bstoi_be_loop s.data         0)
       else .ofNat (bstoi_be_loop s.data.reverse 0)

/-- Truncates `b` by `k` number of characters (bytes). -/
def trunc (b : String) (k : Nat) : String := String.dropRight b k

/-- Extends `b` by `k` number of characters (bytes) of full 1 bits in case `ones` is true (zeroes otherwise). -/
def ext (b : String) (k : Nat) (ones : Bool) : String := String.pushn b (if ones then '\xFF' else '\x00') k

/-- Helper function that truncates or extends a string as necessary. -/
def truncateOrExtend : Bool → String → Nat → Bool → String
  | false, s, n, _    => let m := String.length s; let l := Nat.min m n; trunc s (m - l)
  | true , s, n, ones => let m := String.length s; let l := Nat.max m n; ext   s (l - m) ones

/-- Helper function to extend a binary bitwise operation to Strings.
    Extends the shorter string if `e` is true, otherwise truncates the longer. -/
def byteStringOp (op : Nat → Nat → Nat) (ones e : Bool) (b c : String) : String :=
  let m   := String.length b
  let n   := String.length c
  let b'  := truncateOrExtend e b n ones
  let c'  := truncateOrExtend e c m ones
  let b'' := (·.toUInt8.toNat) <$> String.toList b'
  let c'' := (·.toUInt8.toNat) <$> String.toList c'
  let r   := Function.uncurry op <$> List.zip b'' c''
  ⟨Char.ofNat <$> r⟩

/-- Performs bitwise `and` on bytestrings, extending the lengths if the bool argument is true. -/
def andByteString : Bool → String → String → String := byteStringOp (· &&& ·) true
/-- Performs bitwise `or` on bytestrings, extending the lengths if the bool argument is true. -/
def  orByteString : Bool → String → String → String := byteStringOp (· ||| ·) false
/-- Performs bitwise `xor` on bytestrings, extending the lengths if the bool argument is true. -/
def xorByteString : Bool → String → String → String := byteStringOp (· ^^^ ·) false

/-- Performs bitwise complementer calculation on the input bytestring. -/
def complementByteString (b : String) : String := xorByteString false (String.map (λ _ => '\xFF') b) b

/- Generates a bit sequence from a bytestring.
   Tail recursive version, uses accumulator for the calculation. -/
def bitSequenceFromByteString : List Char → List Bool → List Bool
  | []    , acc => acc
  | c :: t, acc =>
      let b   := c |> Char.toUInt8 |> UInt8.toBitVec
      let bcc := [b.getLsb 7, b.getLsb 6, b.getLsb 5, b.getLsb 4, b.getLsb 3, b.getLsb 2, b.getLsb 1, b.getLsb 0]
      bitSequenceFromByteString t (acc ++ bcc)

/-- Reconstruct a Natural number from it's base-2 big-endian representation.
    Tail recursive version, uses accumulator for the calculation. -/
def reconstructNat : List Bool → Nat → Nat
  | false :: t, acc => reconstructNat t (2 * acc)
  | true  :: t, acc => reconstructNat t (2 * acc + 1)
  | []        , acc => acc

/-- Generates a bytestring from a bit sequence.
    Tail recursive version, uses accumulator for the calculation. -/
def bitSequenceToByteString : List Bool → List Char → Option (List Char)
  | b₇ :: b₆ :: b₅ :: b₄ :: b₃ :: b₂ :: b₁ :: b₀ :: t, acc =>
      bitSequenceToByteString t (Char.ofNat (reconstructNat [b₇, b₆, b₅, b₄, b₃, b₂, b₁, b₀] 0) :: acc)
  | []                                               , acc => .some (List.reverse acc)
  | _                                                , _   => .none

/-- Shifts the bits of `s`
    - `k` places to the left if `k ≥ 0`
    - `k` places to the right if `k < 0` -/
def shiftByteString (s : String) (k : Integer) : String :=
  let bs  := bitSequenceFromByteString s.data []
  let l   := List.length bs
  let bs' := match k with
             | .ofNat n   => if n < l then List.drop n (bs ++ List.replicate n false)
                                      else List.replicate l false
             | .negSucc n => if n + 1 < l then List.take l (List.replicate (n + 1) false ++ bs)
                                          else List.replicate l false
  match bitSequenceToByteString bs' [] with
  | .some x => ⟨x⟩
  | _       => unreachable!

/-- Rotates the bits of `s`
    - `k` places to the left if `k ≥ 0`
    - `k` places to the right if `k < 0` -/
def rotateByteString (s : String) (k : Integer) : String :=
  let bs  := bitSequenceFromByteString s.data []
  let l   := List.length bs
  let bs' := match k with
             | .ofNat n   => List.take l (List.drop (n % l)             (bs ++ bs))
             | .negSucc n => List.take l (List.drop (l - ((n + 1) % l)) (bs ++ bs))
  match bitSequenceToByteString bs' [] with
  | .some x => ⟨x⟩
  | _       => unreachable!

/-- Counts the number of set bits (1) in `s`. -/
def countSetBits (s : String) : Integer :=
  List.count true (bitSequenceFromByteString s.data [])

/-- Finds the index of the first set bit (1) in a bytestring from the _right_.
    Returns -1, if no bits are set. -/
def findFirstSetBit (s : String) : Integer :=
  match bitSequenceFromByteString s.data [] |> List.reverse |> List.findIdx? (·) with
  | .some i => .ofNat i
  | .none   => -1

/-- Returns the value of the nth bit in the bytestring.
    Bits are indexed from the _right_. -/
def readBit : String → Integer → Except String Bool
  | _, .negSucc _ => throw "readBit: index out of bounds"
  | s, .ofNat   i =>
      let len := String.length s
      if 8 * len ≤ i then throw "readBit: index out of bounds"
      else
        let bigIx      := i / 8
        have h : 8 > 0 := by simp
        let littleIx   := ⟨i % 8, Nat.mod_lt i h⟩
        let flipIx     := len - bigIx - 1
        pure (BitVec.getLsb (s.data[flipIx]! |> Char.toUInt8 |> UInt8.toBitVec) littleIx)

def writeBit : String → Integer → Bool → Except String String
  | _, .negSucc _, _ => throw "writeBits: index out of bounds"
  | s, .ofNat   i, x =>
      let len := String.length s
      if 8 * len ≤ i then throw "writeBits: index out of bounds"
      else
        let bigIx    := i / 8
        let littleIx := i % 8
        let flipIx   := len - bigIx - 1
        let bs       := s.data[flipIx]! |> Char.toUInt8 |> UInt8.toNat
        let mask     := 0x1 <<< littleIx
        let bs'      := if x then bs ||| mask
                               else bs &&& (mask ^^^ 0xFF)
        pure ⟨List.set s.data flipIx (bs' |> Char.ofNat)⟩

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
      else pure ⟨List.replicate l (Char.ofNat b)⟩

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
  )

end PlutusCore.Bitwise
