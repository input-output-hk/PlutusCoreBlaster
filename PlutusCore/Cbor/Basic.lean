import PlutusCore.Integer
import PlutusCore.Data

namespace PlutusCore.Cbor

open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

-- Spec from herein refers to the Formal Specification of the Plutus Core Language
-- found at https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf

namespace CborInternal

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

/-- Some sequences are encoded without a specified -/
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
         if (0 ≤ i) && (i ≤   6) then encodeHead 6 (121 + i |> Int.toNat)
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

end CborInternal

export CborInternal
  ( -- encoding
    encodeBytestring
    encodeInt
    encodeData
  )

end PlutusCore.Cbor
