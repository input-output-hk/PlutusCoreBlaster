import PlutusCore.Bitwise
import PlutusCore.ByteString
import PlutusCore.Cbor
import PlutusCore.String

/-! # The `Char`-based byte-level builtins, as they were before `PlutusCore.Bytes`

Verbatim copies of the definitions that `consByteString*`, `sliceByteString`, `indexByteString`,
`integerToByteString`, `byteStringToInteger`, `encodeUtf8`, `decodeUtf8`, `serialiseData`
(`encodeData`) and the logical and bitwise builtins had before they were rewritten over
`PlutusCore.Bytes`. `Tests.ByteString.Tests` checks the rewritten builtins against them.
-/

namespace Tests.ByteString.Reference

open PlutusCore.Integer
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.String (utf8EncodeChar utf8DecodeChar?)

/-! ## `ByteString` -/

def consByteStringV1 (n : Integer) (bs : ByteString) : ByteString :=
  match (modInteger n 256) with
  | Except.ok m => ByteString.cons m.toNat.toUInt8 bs
  | Except.error _ => unreachable!

def consByteStringV2 (n : Integer) (bs : ByteString) : Except String ByteString :=
  if 0 <= n && n <= 255
  then pure (ByteString.cons n.toNat.toUInt8 bs)
  else throw "consByteStringV2: invalid byte representation"

def sliceByteString (s : Integer) (k : Integer) (bs : ByteString) : ByteString :=
  -- Haskell semantics: take (max 0 k) (drop (max 0 s) bs)
  -- Negative offsets are clamped to 0; the end is start + count (not s + k).
  let start := (Max.max s (0 : Integer)).toNat
  let count := (Max.max k (0 : Integer)).toNat
  let subString := (bs.data.toList.drop start).take count
  {data := String.mk subString }

def indexByteString (bs : ByteString) (j : Integer) : Except String Integer :=
  if j < 0 then throw s!"indexByteString: index out of bounds"
  else
    match bs.data.toList[j.toNat]? with
    | none => throw s!"indexByteString: index out of bounds"
    | some c => pure c.toNat

/-! ## `integerToByteString` and `byteStringToInteger` -/

open PlutusCore.Bitwise.BitwiseInternal (integerLog2 integerWidth maxOutputLength maxOutputBitsLength)

def itobs_be_loop : Nat → List Char → Nat → Except String (List Char)
  | .succ p, a, n => itobs_be_loop p (Char.ofNat (n % 256) :: a) (n / 256)
  | .zero  , a, 0 => pure a
  | .zero  , _, _ => throw "integerToByteString: cannot represent Integer in given number of bytes"

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

def bstoi_be_loop : List Char → Nat → Nat
  | []    , acc => acc
  | h :: t, acc => bstoi_be_loop t (acc * 256 + (Char.toNat h))

/-- The `byteStringToInteger` function converts bytestrings to non-negative integers. -/
def byteStringToInteger (e : Bool) (s : String) : Integer :=
  if e then .ofNat (bstoi_be_loop s.data         0)
       else .ofNat (bstoi_be_loop s.data.reverse 0)

/-! ## UTF-8 -/

def encodeUtf8 (s : String) : ByteString := ⟨⟨s.data.flatMap utf8EncodeChar⟩⟩

def decodeUtf8 (bs : ByteString) : Except String String :=
  loop 0 bs.length bs.data.toList ""
where
  loop (i : Nat) (e : Nat) (bs : List Char) (acc : String) : Except String String :=
    if _h : i < e then
      match utf8DecodeChar? bs i with
      | none => throw "decodeUtf8: invalid ByteString"
      | some c =>
          loop (i + c.utf8Size) e bs (acc.push c)
    else pure acc
  termination_by e - i
  decreasing_by
    have := Nat.sub_lt_sub_left _h (Nat.add_lt_add_left c.utf8Size_pos i)
    decreasing_tactic

/-! ## CBOR encoding of `Data` -/

/-- Returns the `i`th byte of `n` in little-endian ordering -/
-- Spec B.4. 𝖻_𝑖(𝑛) = 𝗆𝗈𝖽(𝖽𝗂𝗏(𝑛, 256 ^ 𝑖), 256)
@[simp]
def b_ (i n : Nat) : Char := Char.ofNat ((n / (256 ^ i)) % 256)

/-- e_w: Returns the little-endian encoding of natural numbers in the prescribed width.
    in CBOR only the forms e₁ e₂ e₄ and e₈ are used. -/
-- Spec B.4. 𝖾_𝑘(𝑛) = [𝖻_(𝑘−1)(𝑛), … , 𝖻_0(𝑛)] if 𝑛 ≤ 256 ^ 𝑘 − 1.
@[simp] def e₁ (n : Nat) : List Char := [b_ 0 n]
@[simp] def e₂ (n : Nat) : List Char := [b_ 1 n, b_ 0 n]
@[simp] def e₄ (n : Nat) : List Char := [b_ 3 n, b_ 2 n, b_ 1 n, b_ 0 n]
@[simp] def e₈ (n : Nat) : List Char := [b_ 7 n, b_ 6 n, b_ 5 n, b_ 4 n, b_ 3 n, b_ 2 n, b_ 1 n, b_ 0 n]

/-- ε_head: Encodes the major type (`m`) × Nat pair -/
-- Spec B.4.
def encodeHead (m n : Nat) (_h1 : m ≤ 7) (_h2 : n ≤ 18446744073709551615) : List Char :=
 if n ≤                   23 then [Char.ofNat (32 * m + n)]
 else if n ≤                  255 then Char.ofNat (32 * m + 24) :: e₁ n
 else if n ≤                65535 then Char.ofNat (32 * m + 25) :: e₂ n
 else if n ≤           4294967295 then Char.ofNat (32 * m + 26) :: e₄ n
 else
   -- case when n ≤ 18446744073709551615
   Char.ofNat (32 * m + 27) :: e₈ n

/-- Helper theorem used in  the termination proof for `splitToChunks` -/
theorem String.data_length_of_nonEmpty_pos (s : String) (h : s ≠ "") : 0 < List.length s.data := by
  obtain ⟨data⟩ := s
  induction data
  · contradiction
  · simp

/-- Helper theorem used in  the termination proof for `splitToChunks` -/
theorem String.drop_decreases_data_length (s : String) (n : Nat) (hs : s ≠ "") (hn : 0 < n) : (List.drop n s.data).length < s.data.length := by
    have hs0 : 0 < List.length s.data := String.data_length_of_nonEmpty_pos s hs
    simp
    omega

def splitToChunksLoop (acc : List String) (s : String) : List String :=
  if s = "" then List.reverse acc
            else splitToChunksLoop (⟨List.take 64 s.data⟩ :: acc) ⟨List.drop 64 s.data⟩

  termination_by (List.length s.data)
  decreasing_by
    apply String.drop_decreases_data_length <;> try assumption
    omega

/-- Splitting strings to chunks as it is implemented in Plutus and stated in the spec. -/
-- Spec B.5. "Canonical 64-byte decomposition"
def splitToChunks := splitToChunksLoop []

/-- Helper for `split_to_chunks_elem_leq_64`: every chunk produced by the loop has
    length at most 64, provided every string already accumulated does. -/
theorem splitToChunksLoop_elem_leq_64 (acc : List String) (s : String)
    (hacc : ∀ e ∈ acc, e.length ≤ 64) :
    ∀ e ∈ splitToChunksLoop acc s, e.length ≤ 64 := by
  fun_induction splitToChunksLoop acc s with
  | case1 acc =>
    simpa using hacc
  | case2 acc s hs ih =>
    apply ih
    intro e he
    rcases List.mem_cons.mp he with h | h
    · subst h
      simp [String.length]
      omega
    · exact hacc e h

theorem split_to_chunks_elem_leq_64 (s : String) (e : String) (h : e ∈ splitToChunks s) : e.length ≤ 64 := by
  exact splitToChunksLoop_elem_leq_64 [] s (by simp) e h

/-- Some sequences are encoded without a specified length (indefinite length encoding). -/
-- Spec B.4. Heads for indefinite-length items.
def encodeIndef (m : Nat) : Char := Char.ofNat (32 * m + 31)

/-- Encodes a string chunk -/
-- Spec B.5. ε_B*
def encodeBytestringChunk (s : String) (h : s.length ≤ 64) : List Char :=
  (encodeHead 2 s.length (by decide) (Nat.le_trans h (by decide))) ++ s.data

/-- Encodes a bytestring.
    Note: it first splits the byte string to 64 byte chunks
          as detailed in the specification. -/
-- Spec B.5. ε_B*
def encodeBytestring (s : String) : String :=
  match heq : splitToChunks s with
  | []      => String.mk (encodeHead 2 0 (by decide) (by decide)) -- empty bytestring is a definite 0-length string (0x40)
  | h :: [] => String.mk (encodeBytestringChunk h (split_to_chunks_elem_leq_64 s h (by simp [heq])))
  | chunks  =>
      String.mk (encodeIndef 2 :: List.concat
        (encode_chunks chunks (heq ▸ split_to_chunks_elem_leq_64 s)) '\xFF')
where
  encode_chunks (xs : List String) (hxs : ∀ c ∈ xs, c.length ≤ 64) : List Char :=
    match xs with
    | [] => []
    | c :: xs' =>
       let cs := encodeBytestringChunk c (List.forall_mem_cons.mp hxs).1
       cs ++ encode_chunks xs' (List.forall_mem_cons.mp hxs).2

/-- Encodes a natural number as a list of characters in big-endian -/
-- Spec B.6. itos
def itos (n : Nat) : String :=
  if n == 0
    then ""
    else itos (n / 256) ++ String.singleton (Char.ofNat (n % 256))

  decreasing_by
    apply Nat.div_lt_self
    · have h : ¬(n == 0) = true := by assumption
      simp at h
      omega
    · omega

/-- Encodes an integer using zigzag encoding -/
-- Spec B.6. ε_Z
def encodeInt (n : Integer) : String :=
  if h : 0 ≤ n ∧ n ≤ 18446744073709551615 then String.mk (encodeHead 0 (Int.toNat n) (by decide) (by simp [h]))
  else if ( 18446744073709551616 ≤ n) then String.mk (encodeHead 6 2 (by decide) (by decide)) ++ (encodeBytestring (itos (Int.toNat n)))
  else if h : -18446744073709551616 ≤ n ∧ n ≤ -1 then String.mk (encodeHead 1 (Int.toNat (-n - 1)) (by decide) (by simp only [Integer] at h; omega))
  else -- case when n ≤ -18446744073709551617
    (String.mk (encodeHead 6 3 (by decide) (by decide))) ++ (encodeBytestring (itos (Int.toNat (-n - 1))))

/-- Encodes a ctag. -/
-- Spec B.7. ε_ctag
def encodeCtag (i : Integer) : String :=
  if h : 0 ≤ i ∧ i ≤ 6 then String.mk (encodeHead 6 (Int.toNat (121 + i)) (by decide) (by simp only [Integer] at h; omega))
  else if h : 7 ≤ i ∧ i ≤ 127 then String.mk (encodeHead 6 (Int.toNat (1280 + (i - 7))) (by decide) (by simp only [Integer] at h; omega))
  else String.mk ((encodeHead 6 102 (by decide) (by decide)) ++ (encodeHead 4 2 (by decide) (by decide))) ++ (encodeInt i)

-- Spec B.7. Encoding and  decoding Data. ε_data

mutual
/-- Encode data (builtinData). -/
def foldMap (xs : List (Data × Data)) (acc : String) : Option String :=
  match xs with
  | [] => some acc
  | a :: as =>
     match encodeData a.fst, encodeData a.snd with
     | some s1, some s2 => foldMap as (acc ++ s1 ++ s2)
     | _, _ => none

def foldList (xs : List Data) (acc : String) : Option String :=
  match xs with
  | [] => some acc
  | a :: as =>
      match encodeData a with
      | some s => foldList as (acc ++ s)
      | _ => none

def encodeData : Data → Option String
  | .Constr idx fields =>
       if fields.isEmpty then
          -- empty field list is a DEFINITE empty array (0x80), matching the serialiseData builtin
          encodeCtag idx ++ (String.mk (encodeHead 4 0 (by decide) (by decide)))
       else
         if let some s := foldList fields "" then
            encodeCtag idx ++ (String.singleton (encodeIndef 4)) ++ s ++ "\xFF"
         else none
  | .Map mxs =>
       let l := mxs.length
       if h : l ≤ 18446744073709551615 then
         if let some s := foldMap mxs "" then
          String.mk (encodeHead 5 l (by decide) h) ++ s
         else none
       else none
  | .List xs =>
      if xs.isEmpty then
        -- empty list is a DEFINITE empty array (0x80), matching the serialiseData builtin
        String.mk (encodeHead 4 0 (by decide) (by decide))
      else
        if let some s := foldList xs "" then
          (String.singleton (encodeIndef 4)) ++ s ++ "\xFF"
        else none
  | .I i => encodeInt i
  | .B bs => encodeBytestring bs.data

end

/-! ## Logical and bitwise builtins -/

section Bitwise

open PlutusCore.Bitwise.BitwiseInternal (maxOutputLength)

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

end Bitwise

end Tests.ByteString.Reference
