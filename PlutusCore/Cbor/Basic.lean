import PlutusCore.ByteString
import PlutusCore.Integer
import PlutusCore.Data

namespace PlutusCore.Cbor

open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

-- Spec from herein refers to the Formal Specification of the Plutus Core Language
-- found at https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf

namespace CborInternal

-- ==============
-- =  Encoding  =
-- ==============

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
def encodeHead (m n : Nat) : Option (List Char) :=
  if m ≤ 7 then
         if n ≤                   23 then .some [Char.ofNat (32 * m + n)]
    else if n ≤                  255 then .some (Char.ofNat (32 * m + 24) :: e₁ n)
    else if n ≤                65535 then .some (Char.ofNat (32 * m + 25) :: e₂ n)
    else if n ≤           4294967295 then .some (Char.ofNat (32 * m + 26) :: e₄ n)
    else if n ≤ 18446744073709551615 then .some (Char.ofNat (32 * m + 27) :: e₈ n)
    else .none
  else .none

-- TODO: use Fin version after support is implemented in Solver.
-- def encodeHead (m : Fin 8) (n : Fin (256 ^ 8)) : Option (List Char) :=
--        if      n ≤                   23 then .some [Char.ofNat (32 * m + n)]
--   else if h₁ : n ≤                  255 then .some (Char.ofNat (32 * m + 24) :: e₁ (Fin.castLT n (Nat.lt_add_one_of_le h₁)))
--   else if h₂ : n ≤                65535 then .some (Char.ofNat (32 * m + 25) :: e₂ (Fin.castLT n (Nat.lt_add_one_of_le h₂)))
--   else if h₃ : n ≤           4294967295 then .some (Char.ofNat (32 * m + 26) :: e₄ (Fin.castLT n (Nat.lt_add_one_of_le h₃)))
--   else if h₄ : n ≤ 18446744073709551615 then .some (Char.ofNat (32 * m + 27) :: e₈ (Fin.castLT n (Nat.lt_add_one_of_le h₄)))
--   else False.elim (h₄ (Fin.succ_le_succ_iff.mp (Fin.isLt n))) -- absurd case

/-- Helper theorem used in  the termination proof for `splitToChunks` -/
theorem String.data_length_of_nonEmpty_pos (s : String) (h : s ≠ "") : 0 < List.length s.data :=  by
  obtain ⟨data⟩ := s
  induction data
  · contradiction
  · simp

/-- Helper theorem used in  the termination proof for `splitToChunks` -/
theorem String.drop_decreases_data_length (s : String) (n : Nat) (hs : s ≠ "") (hn : 0 < n) : (List.drop n s.data).length < s.data.length := by
    have hs0 : 0 < List.length s.data := String.data_length_of_nonEmpty_pos s hs
    simp
    omega

/-- Splitting strings to chunks as it is implemented in Plutus and stated in the spec. -/
-- Spec B.5. "Canonical 64-byte decomposition"
def splitToChunks (s : String) : List String :=
  if s = "" then []
  else ⟨List.take 64 s.data⟩ :: splitToChunks ⟨List.drop 64 s.data⟩

  termination_by (List.length s.data)
  decreasing_by
    apply String.drop_decreases_data_length <;> try assumption
    omega

/-- Some sequences are encoded without a specified length (indefinite length encoding). -/
-- Spec B.4. Heads for indefinite-length items.
def encodeIndef (m : Nat) : Char := Char.ofNat (32 * m + 31)

/-- Encodes a string chunk -/
-- Spec B.5. ε_B*
def encodeBytestringChunk (s : String) : Option (List Char) := do
  let length := List.length s.data
  if length ≤ 256 ^ 8
    then .some ((←encodeHead 2 length) ++ s.data)
    else .none

/-- Encodes a bytestring.
    Note: it first splits the byte string to 64 byte chunks
          as detailed in the specification. -/
-- Spec B.5. ε_B*
def encodeBytestring (s : String) : Option String :=
  match splitToChunks s with
  | []      => .some ""
  | h :: [] => String.mk <$> encodeBytestringChunk h
  | chunks  => do .some ⟨encodeIndef 2 :: (List.concat (←List.flatMapM encodeBytestringChunk chunks) '\xFF')⟩


/-- Encodes a natural number as a list of characters in big-endian -/
-- Spec B.6. itos
def itos (n : Nat) : String :=
  if n == 0
    then ""
    else itos (n / 256) ++ (n % 256 |> Char.ofNat |> String.singleton)

  decreasing_by
    apply Nat.div_lt_self
    · have h : ¬(n == 0) = true := by assumption
      simp at h
      omega
    · omega

/-- Encodes an integer using zigzag encoding -/
-- Spec B.6. ε_Z
def encodeInt (n : Integer) : Option String :=
       if (                    0 ≤ n) && (n ≤  18446744073709551615) then String.mk <$> encodeHead 0 (Int.toNat n)
  else if ( 18446744073709551616 ≤ n                               ) then do (String.mk (←encodeHead 6 2)) ++ (←encodeBytestring (n |> Int.toNat |> itos))
  else if (-18446744073709551616 ≤ n) && (n ≤                    -1) then String.mk <$> encodeHead 1 ((-n - 1) |> Int.toNat)
  else if (                               n ≤ -18446744073709551617) then do (String.mk (←encodeHead 6 3)) ++ (←encodeBytestring (-n - 1 |> Int.toNat |> itos))
  else .none

/-- Encodes a ctag. -/
-- Spec B.7. ε_ctag
def encodeCtag (i : Integer) : Option String :=
  String.mk <$>
         if (0 ≤ i) && (i ≤   6) then encodeHead 6 (121 + i        |> Int.toNat)
    else if (7 ≤ i) && (i ≤ 127) then encodeHead 6 (1280 + (i - 7) |> Int.toNat)
    else do (←encodeHead 6 102) ++ (←encodeHead 4 2) ++ ((←encodeInt i).data)

/-- Encode data (builtinData). -/
-- Spec B.7. Encoding and  decoding Data. ε_data
def encodeData : Data → Option String
  | .Constr idx fields => do
      (←encodeCtag idx)
      ++ (encodeIndef 4 |> String.singleton)
      ++ (←List.foldlM (λ s a => do .some (s ++ (←encodeData a))) "" fields)
      ++ "\xFF"
  | .Map mxs => do
      String.mk (←encodeHead 5 (List.length mxs))
      ++ (←List.foldlM (λ s p => do .some (s ++ (←encodeData p.fst) ++ (←encodeData p.snd))) "" mxs)
  | .List xs => do
      (encodeIndef 4 |> String.singleton)
      ++ (←List.foldlM (λ s a => do .some (s ++ (←encodeData a))) "" xs)
      ++ "\xFF"
  | .I i => encodeInt i
  | .B bs => encodeBytestring bs.data

  decreasing_by
    · have : sizeOf a < sizeOf fields := by apply List.sizeOf_lt_of_mem; assumption
      simp; omega
    · have : sizeOf p.fst < sizeOf p   := by induction p; simp; omega
      have : sizeOf p     < sizeOf mxs := by apply List.sizeOf_lt_of_mem; assumption
      simp; omega
    · have : sizeOf p.snd < sizeOf p   := by induction p; simp; omega
      have : sizeOf p     < sizeOf mxs := by apply List.sizeOf_lt_of_mem; assumption
      simp; omega
    · have : sizeOf a < sizeOf xs := by apply List.sizeOf_lt_of_mem; assumption
      simp; omega

-- ==============
-- =  Decoding  =
-- ==============

/-- Helper function that is used in reconstructing natural numbers from their big endian representation -/
def d_ (i : Nat) (c : Char) := (Char.toNat c) * (256 ^ i)

-- Spec B.4. The `d_k` function is a general function to reconstruct a `k` byte natural number
-- from its big endian representation. In the spec only the forms with k = 1, 2, 4 and 8 are used.
/-- Decodes a one byte integer. -/
def d₁ : List Char → Option (List Char × Nat)
  | b :: t => .some (t, Char.toNat b)
  | []     => .none

/-- Decodes a two byte integer. -/
def d₂ : List Char → Option (List Char × Nat)
  | b₁ :: b₀ :: t => .some (t, d_ 1 b₁ + d_ 0 b₀)
  | _             => .none

/-- Decodes a four byte integer. -/
def d₄ : List Char → Option (List Char × Nat)
  | b₃ :: b₂ :: b₁ :: b₀ :: t => .some (t, d_ 3 b₃ + d_ 2 b₂ + d_ 1 b₁ + d_ 0 b₀)
  | _                         => .none

/-- Decodes an eight byte integer. -/
def d₈ : List Char → Option (List Char × Nat)
  | b₇ :: b₆ :: b₅ :: b₄ :: b₃ :: b₂ :: b₁ :: b₀ :: t => .some (t, d_ 7 b₇ + d_ 6 b₆ + d_ 5 b₅ + d_ 4 b₄ + d_ 3 b₃ + d_ 2 b₂ + d_ 1 b₁ + d_ 0 b₀)
  | _                                                 => .none

/-- Decodes a "head" structure that describes how the next bytes should be interpreted. -/
-- Spec B.4. D_head
def decodeHead : List Char → Option ((List Char) × Nat × Nat)
  | n' :: s =>
      let n := Char.toNat n'
      let d := n / 32
      match n % 32 with
      | 24 => (λ (s', k) => (s', d, k)) <$> d₁ s
      | 25 => (λ (s', k) => (s', d, k)) <$> d₂ s
      | 26 => (λ (s', k) => (s', d, k)) <$> d₄ s
      | 27 => (λ (s', k) => (s', d, k)) <$> d₈ s
      | m  => if m ≤ 23 then .some (s, d, m)
                        else .none
  | _ => .none

/-- Decodes a "head" structure with indefinite length that describes how the next bytes should be interpreted. -/
-- Spec B.4. D_indef
def decodeIndef : List Char → Option (List Char × Nat)
  | n' :: s =>
      let n := Char.toNat n'
      if n % 32 = 31
        then .some (s, n / 32)
        else .none
  | [] => .none

/-- Decodes (consumes) the next `n` bytes from the input. -/
-- Spec B.5. D_bytes
def decodeBytes : Nat → List Char → Option (List Char × List Char)
  | .zero  , s       => .some (s, [])
  | .succ _, []      => .none
  | .succ p, b :: s' => do
      let (s'', t) ← decodeBytes p s'
      .some (s'', b :: t)

/-- Decodes a definite length "block" (bytestring chunk). -/
-- Spec B.5. D_block
def decodeBlock (s : List Char) : Option (List Char × List Char) := do
  let (s', m, n) ← decodeHead s
  if m = 2 ∧ n ≤ 64
    then decodeBytes n s'
    else .none

/-- Decodes an indefinite number of blocks. This function can be partial as long as
    it is not used in UPLC evaluation. -/
-- Spec B.5. D_blocks
partial def decodeBlocks : List Char → Option (List Char × List Char)
  | '\xFF' :: s' => .some (s', [])
  | s            => do
      let (s' , t ) ← decodeBlock s
      let (s'', t') ← decodeBlocks s'
      .some (s'', t ++ t')

/-- Decodes a bytestring from the input `s`. -/
-- Spec B.5. D_B*
def decodeBytestring (s : String) : Option (String × String) :=
  match decodeBlock s.data with
  | .some (s', t) => .some (⟨s'⟩, ⟨t⟩)
  | .none         => do
      let (s', n) ← decodeIndef s.data
      if n = 2
        then Prod.map String.mk String.mk <$> decodeBlocks s'
        else .none

/-- Decodes a "large" block, which can have a length larger than 64 bytes. -/
def decodeLargeBlock (s : List Char) : Option (List Char × List Char) := do
  let (s', m, n) ← decodeHead s
  if m = 2
    then decodeBytes n s'
    else .none

/-- Decodes a sequence of "large" blocks. -/
partial def decodeLargeBlocks : List Char → Option (List Char × List Char)
  | '\xFF' :: s' => .some (s', [])
  | s            => do
      let (s' , t ) ← decodeLargeBlock s
      let (s'', t') ← decodeLargeBlocks s'
      .some (s'', t ++ t')

/-- Decodes a "large" bytestring, which can have blocks larger than 64 bytes.. -/
def decodeLargeBytestring (s : String) : Option (String × String) :=
  match decodeLargeBlock s.data with
  | .some (s', t) => .some (⟨s'⟩, ⟨t⟩)
  | .none         => do
      let (s', n) ← decodeIndef s.data
      if n = 2
        then Prod.map String.mk String.mk <$> decodeLargeBlocks s'
        else .none

/-- Reconstructs a natural number from its big endian representation. -/
-- Spec B.6. stoi
def stoi (s : String) : Nat :=
  let rec go : List Char → Nat
    | []      => 0
    | n :: l' => 256 * go l' + (Char.toNat n)
  go (List.reverse s.data)

/- Decodes an integer value from input `s`. -/
--  Spec B.6. D_Z
def decodeInt (s : String) : Option (String × Integer) :=
  match decodeHead s.data with
  | .some (s', 0, n) => .some (⟨s'⟩, (Int.ofNat n))
  | .some (s', 1, n) => .some (⟨s'⟩, -(Int.ofNat n) - 1)
  | .some (s', 6, 2) => (λ (s'', b) => (s'', stoi b))                    <$> decodeBytestring ⟨s'⟩
  | .some (s', 6, 3) => (λ (s'', b) => (s'', -(Int.ofNat (stoi b) - 1))) <$> decodeBytestring ⟨s'⟩
  | _                => .none

/- Decodes a ctag from input `s`. -/
-- Spec B.7. D_ctag
def decodeCtag (s : List Char) : Option (List Char × Integer) :=
  match decodeHead s with
  | .some (s', 6, 102) => do
      let (s'', m, n) ← decodeHead s'
      if m = 4 ∧ n = 2
        then Prod.map String.data id <$> decodeInt ⟨s''⟩
        else .none
  | .some (s', 6, i) =>      if  121 ≤ i ∧ i ≤  127 then .some (s', i - 121)
                        else if 1280 ≤ i ∧ i ≤ 1400 then .some (s', (i - 1280) + 7)
                        else .none
  | _ => .none

/- Tries to decode a value from `s` using `f`. If fails it tries `g` with the same input. Fails if both fails. -/
def decodeAlternative {α β : Type} (f : List Char → Option (List Char × α)) (g : List Char → Option (List Char × β)) (s : List Char) : Option (List Char × (α ⊕ β)) :=
  match f s with
  | .some (s', a) => .some (s', .inl a)
  | .none         => (λ (s', b) => (s', .inr b)) <$> g s

/- Decodes a builtin data from input `s`. -/
-- Spec B.7. D_data
partial def decodeData (s : String) : Option (String × Data) :=
    Prod.map String.mk id <$> decodeDataLoop s.data
  where
    decodeDataLoop (s : List Char) : Option (List Char × Data) :=
      match decodeAlternative decodeIndef decodeHead s with
      | .some (_ , .inl 2)      => Prod.map String.data (.B ∘ ByteString.mk) <$> decodeBytestring ⟨s⟩
      | .some (s', .inl 4     ) => Prod.map id          .List                <$> decodeListIndef s'
      | .some (_ , .inr (0, _))
      | .some (_ , .inr (1, _))
      | .some (_ , .inr (6, 2))
      | .some (_ , .inr (6, 3)) => Prod.map String.data .I                   <$> decodeInt ⟨s⟩
      | .some (_ , .inr (2, _)) => Prod.map String.data (.B ∘ ByteString.mk) <$> decodeBytestring ⟨s⟩
      | .some (s', .inr (4, n)) => Prod.map id          .List                <$> decodeList n s'
      | .some (s', .inr (5, n)) => Prod.map id          .Map                 <$> decodePairList n s'
      | .some (_ , .inr (6, _)) =>                                               decodeConstr s
      | _ => .none

    decodeList : Nat → List Char → Option (List Char × List Data)
      | .zero  , s => .some (s, [])
      | .succ p, s => do
          let (s' , d) ← decodeDataLoop s
          let (s'', l) ← decodeList p s'
          .some (s'', d :: l)

    decodeListIndef : List Char → Option (List Char × List Data)
      | '\xFF' :: s' => .some (s', [])
      | s            => do
          let (s' , d) ← decodeDataLoop s
          let (s'', l) ← decodeListIndef s'
          .some (s'', d :: l)

    decodePairList : Nat → List Char → Option (List Char × List (Data × Data))
      | .zero  , s => .some (s, [])
      | .succ p, s => do
          let (s'  , k) ← decodeDataLoop s
          let (s'' , d) ← decodeDataLoop s'
          let (s''', l) ← decodePairList p s''
          .some (s''', (k, d) :: l)

    decodeConstr (s : List Char) : Option (List Char × Data) := do
      let (s' , i) ← decodeCtag s
      let (s'', r) ← decodeAlternative decodeIndef decodeHead s'
      match r with
      | .inl 4      => Prod.map id (.Constr i) <$> decodeListIndef s''
      | .inr (4, n) => Prod.map id (.Constr i) <$> decodeList n s''
      | _           => .none

end CborInternal

export CborInternal
  ( -- encoding
    encodeBytestring
    encodeInt
    encodeData
    -- decoding
    decodeBytestring
    decodeLargeBytestring
    decodeInt
    decodeData
  )

end PlutusCore.Cbor
