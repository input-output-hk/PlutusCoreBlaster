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
  else if ( 18446744073709551616 ≤ n)                                then do (String.mk (←encodeHead 6 2)) ++ (←encodeBytestring (n |> Int.toNat |> itos))
  else if (-18446744073709551616 ≤ n) && (n ≤                    -1) then String.mk <$> encodeHead 1 ((-n - 1) |> Int.toNat)
  else if                                (n ≤ -18446744073709551617) then do (String.mk (←encodeHead 6 3)) ++ (←encodeBytestring (-n - 1 |> Int.toNat |> itos))
  else .none

/-- Encodes a ctag. -/
-- Spec B.7. ε_ctag
def encodeCtag (i : Integer) : Option String :=
  String.mk <$>
         if (0 ≤ i) && (i ≤   6) then encodeHead 6 ( 121 + i       |> Int.toNat)
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
      ((←encodeHead 5 (List.length mxs)) |> String.mk)
      ++ (←List.foldlM (λ s p => do .some (s ++ (←encodeData p.fst) ++ (←encodeData p.snd))) "" mxs)
  | .List xs => do
      (encodeIndef 4 |> String.singleton)
      ++ (←List.foldlM (λ s a => do .some (s ++ (←encodeData a))) "" xs)
      ++ "\xFF"
  | .I i => encodeInt i
  | .B bs => encodeBytestring bs.data

  decreasing_by
    · have : sizeOf a     < sizeOf fields := by apply List.sizeOf_lt_of_mem; assumption
      simp; omega
    · have : sizeOf p.fst < sizeOf p      := by induction p; simp; omega
      have : sizeOf p     < sizeOf mxs    := by apply List.sizeOf_lt_of_mem; assumption
      simp; omega
    · have : sizeOf p.snd < sizeOf p      := by induction p; simp; omega
      have : sizeOf p     < sizeOf mxs    := by apply List.sizeOf_lt_of_mem; assumption
      simp; omega
    · have : sizeOf a     < sizeOf xs     := by apply List.sizeOf_lt_of_mem; assumption
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

def decodeBytesLoop (acc : List Char) : Nat → List Char → Option (List Char × List Char)
  | .zero  , s       => .some (s, (List.reverse acc))
  | .succ _, []      => .none
  | .succ p, b :: s' => decodeBytesLoop (b :: acc) p s'

/-- Decodes (consumes) the next `n` bytes from the input. -/
-- Spec B.5. D_bytes
def decodeBytes := decodeBytesLoop []

/-- Decodes a definite length "block" (bytestring chunk). -/
-- Spec B.5. D_block
def decodeBlock (s : List Char) : Option (List Char × List Char) := do
  let (s', m, n) ← decodeHead s
  if m = 2 ∧ n ≤ 64
    then decodeBytes n s'
    else .none

-- ==========================
-- = Termination Helpers    =
-- ==========================

/-- Helper theorem: decodeHead always consumes at least one byte on success -/
theorem decodeHead_consumes (s : List Char) :
  ∀ s' d k, decodeHead s = some (s', d, k) → s'.length < s.length := by
  intro s' d k h
  unfold decodeHead at h
  cases s with
  | nil => simp at h
  | cons n' t =>
    simp at h
    split at h
    · -- Case: n % 32 = 24, uses d₁
      simp [Option.map_eq_some_iff, d₁] at h
      obtain ⟨b, heq⟩ := h
      cases t with
      | nil => simp at heq
      | cons c t' =>
        simp at heq
        obtain ⟨h1, h2, h3, h4, h5⟩ := heq
        obtain ⟨h2a, h2b⟩ := h2
        rw [← h3, ← h2a]
        simp; omega
    · -- Case: n % 32 = 25, uses d₂
      simp [Option.map_eq_some_iff, d₂] at h
      obtain ⟨b, heq⟩ := h
      cases t with
      | nil => simp at heq
      | cons c1 t1 =>
        cases t1 with
        | nil => simp at heq
        | cons c0 t' =>
          simp at heq
          obtain ⟨h1, h2, h3, h4, h5⟩ := heq
          obtain ⟨h2a, h2b⟩ := h2
          rw [← h3, ← h2a]
          simp; omega
    · -- Case: n % 32 = 26, uses d₄
      simp [Option.map_eq_some_iff, d₄] at h
      obtain ⟨b, heq⟩ := h
      cases t with
      | nil => simp at heq
      | cons c3 t3 =>
        cases t3 with
        | nil => simp at heq
        | cons c2 t2 =>
          cases t2 with
          | nil => simp at heq
          | cons c1 t1 =>
            cases t1 with
            | nil => simp at heq
            | cons c0 t' =>
              simp at heq
              obtain ⟨h1, h2, h3, h4, h5⟩ := heq
              obtain ⟨h2a, h2b⟩ := h2
              rw [← h3, ← h2a]
              simp; omega
    · -- Case: n % 32 = 27, uses d₈
      simp [Option.map_eq_some_iff, d₈] at h
      obtain ⟨b, heq⟩ := h
      cases t with
      | nil => simp at heq
      | cons c7 t7 =>
        cases t7 with
        | nil => simp at heq
        | cons c6 t6 =>
          cases t6 with
          | nil => simp at heq
          | cons c5 t5 =>
            cases t5 with
            | nil => simp at heq
            | cons c4 t4 =>
              cases t4 with
              | nil => simp at heq
              | cons c3 t3 =>
                cases t3 with
                | nil => simp at heq
                | cons c2 t2 =>
                  cases t2 with
                  | nil => simp at heq
                  | cons c1 t1 =>
                    cases t1 with
                    | nil => simp at heq
                    | cons c0 t' =>
                      simp at heq
                      obtain ⟨h1, h2, h3, h4, h5⟩ := heq
                      obtain ⟨h2a, h2b⟩ := h2
                      rw [← h3, ← h2a]
                      simp; omega
    · -- Case: m ≤ 23
      split at h
      · simp at h
        obtain ⟨h1, h2, h3⟩ := h
        rw [← h1]
        simp
      · simp at h

/-- Helper theorem: decodeBytesLoop consumes exactly n bytes regardless of accumulator -/
theorem decodeBytesLoop_consumes : ∀ (acc : List Char) (n : Nat) (s : List Char) (s' t : List Char),
  decodeBytesLoop acc n s = some (s', t) → s'.length + n = s.length := by
  intro acc n s s' t h
  revert acc s s' t
  induction n with
  | zero =>
    intro acc s s' t h
    unfold decodeBytesLoop at h
    simp at h
    obtain ⟨h1, _⟩ := h
    rw [← h1]; simp
  | succ p ih =>
    intro acc s s' t h
    cases s with
    | nil => unfold decodeBytesLoop at h; simp at h
    | cons b s'' =>
      unfold decodeBytesLoop at h
      have ih_result := ih (b :: acc) s'' s' t h
      simp
      calc s'.length + (p + 1)
        = s'.length + p + 1 := by omega
        _ = s''.length + 1 := by rw [ih_result]

/-- Helper theorem: decodeBytes consumes exactly n bytes on success -/
theorem decodeBytes_consumes (n : Nat) (s : List Char) :
  ∀ s' t, decodeBytes n s = some (s', t) → s'.length + n = s.length := by
  intro s' t h
  unfold decodeBytes at h
  exact decodeBytesLoop_consumes [] n s s' t h

/-- Helper theorem: decodeBlock consumes at least one byte on success -/
theorem decodeBlock_consumes (s : List Char) :
  ∀ s' t, decodeBlock s = some (s', t) → s'.length < s.length := by
  intro s' t h
  unfold decodeBlock at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨s'', m, n⟩, hdh, h⟩ := h
  split at h
  · have h_head := decodeHead_consumes s s'' m n hdh
    have h_bytes := decodeBytes_consumes n s'' s' t h
    omega
  · simp at h

/-- Helper theorem: decodeIndef consumes exactly one byte on success -/
theorem decodeIndef_consumes (s : List Char) :
  ∀ s' n, decodeIndef s = some (s', n) → s'.length + 1 = s.length := by
  intro s' n h
  unfold decodeIndef at h
  cases s with
  | nil => simp at h
  | cons head tail =>
    split at h
    · rename_i b t heq
      simp at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨h2a, h2b⟩ := h2
      subst h2a
      cases heq
      simp
    · simp at h

set_option linter.unusedVariables false

def decodeBlocksLoop (acc : List Char) : (s : List Char) → Option (List Char × List Char)
  | '\xFF' :: s' => .some (s', List.reverse acc)
  | s => match h : decodeBlock s with
      | some (s', t) => decodeBlocksLoop ((List.reverse t) ++ acc) s'
      | none => none
termination_by s => s.length
decreasing_by
  simp_wf
  have : s'.length < s.length := decodeBlock_consumes s s' t h
  exact this

set_option linter.unusedVariables true

/-- Decodes an indefinite number of blocks. -/
-- Spec B.5. D_blocks
def decodeBlocks := decodeBlocksLoop []

/-- Helper theorem: decodeBlocksLoop consumes bytes when recursing. -/
theorem decodeBlocksLoop_consumes :
  ∀ (n : Nat) (acc s s' : List Char) (t : List Char),
    s.length ≤ n → decodeBlocksLoop acc s = some (s', t) → s'.length < s.length := by
  intro n
  induction n with
  | zero =>
    intro acc s s' t hs h
    cases s with
    | nil =>
      unfold decodeBlocksLoop at h
      split at h <;> contradiction
    | cons _ _ => simp at hs
  | succ n' ih =>
    intro acc s s' t hs h
    match s with
    | [] =>
      unfold decodeBlocksLoop at h
      split at h <;> contradiction
    | c :: rest =>
      unfold decodeBlocksLoop at h
      split at h
      · -- Case: c = '\xFF'
        rename_i s'' heq
        simp at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        injection heq with heq_c heq_rest
        subst heq_rest
        simp
      · -- Case: c ≠ '\xFF', must use decodeBlock
        split at h
        · -- decodeBlock succeeds and recurses
          rename_i s'' t' hdb
          have h_block : s''.length < (c :: rest).length := decodeBlock_consumes (c :: rest) s'' t' hdb
          have hs'' : s''.length ≤ n' := by
            have : (c :: rest).length = rest.length + 1 := by simp
            rw [this] at hs
            omega
          have h_rec : s'.length < s''.length := ih ((List.reverse t') ++ acc) s'' s' t hs'' h
          omega
        · -- decodeBlock fails
          contradiction

/-- Helper theorem: decodeBlocks consumes at least one byte on success. -/
theorem decodeBlocks_consumes : ∀ s s' t, decodeBlocks s = some (s', t) → s'.length < s.length := by
  intro s s' t h
  unfold decodeBlocks at h
  exact decodeBlocksLoop_consumes s.length [] s s' t (Nat.le_refl _) h

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

/-- Helper theorem: decodeBytestring consumes at least one byte on success -/
theorem decodeBytestring_consumes (s : String) :
  ∀ s' t, decodeBytestring s = some (s', t) → s'.data.length < s.data.length := by
  intro s' t h
  unfold decodeBytestring at h
  split at h
  · -- Case: decodeBlock succeeds
    rename_i s'' t' hdb
    simp at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1]
    simp
    exact decodeBlock_consumes s.data s'' t' hdb
  · -- Case: decodeBlock fails, try decodeIndef + decodeBlocks
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s'', n⟩, hdi, h_rest⟩ := h
    split at h_rest
    · cases h_blocks : decodeBlocks s'' with
      | none => simp [h_blocks] at h_rest
      | some res =>
        simp [Prod.map, h_blocks] at h_rest
        obtain ⟨h_eq1, h_eq2⟩ := h_rest
        rw [← h_eq1]
        simp
        have h1 := decodeIndef_consumes s.data s'' n hdi
        have h2 := decodeBlocks_consumes s'' res.1 res.2 h_blocks
        omega
    · simp at h_rest

/-- Decodes a "large" block, which can have a length larger than 64 bytes. -/
def decodeLargeBlock (s : List Char) : Option (List Char × List Char) := do
  let (s', m, n) ← decodeHead s
  if m = 2
    then decodeBytes n s'
    else .none

/-- Helper theorem: decodeLargeBlock consumes at least one byte on success -/
theorem decodeLargeBlock_consumes (s : List Char) :
  ∀ s' t, decodeLargeBlock s = some (s', t) → s'.length < s.length := by
  intro s' t h
  unfold decodeLargeBlock at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨s'', m, n⟩, hdh, h⟩ := h
  split at h
  · have h_head := decodeHead_consumes s s'' m n hdh
    have h_bytes := decodeBytes_consumes n s'' s' t h
    omega
  · simp at h

set_option linter.unusedVariables false

def decodeLargeBlocksLoop (acc : List Char) : List Char → Option (List Char × List Char)
  | '\xFF' :: s' => .some (s', List.reverse acc)
  | s            => match h : decodeLargeBlock s with
      | some (s', t) => decodeLargeBlocksLoop ((List.reverse t) ++ acc) s'
      | none => none
termination_by s => s.length
decreasing_by
  simp_wf
  have := decodeLargeBlock_consumes s s' t h
  omega

set_option linter.unusedVariables true

/-- Decodes a sequence of "large" blocks. -/
def decodeLargeBlocks := decodeLargeBlocksLoop []

/-- Decodes a "large" bytestring, which can have blocks larger than 64 bytes. -/
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
  | .some (s', 0, n) => .some (⟨s'⟩,  (Int.ofNat n)    )
  | .some (s', 1, n) => .some (⟨s'⟩, -(Int.ofNat n) - 1)
  | .some (s', 6, 2) => (λ (s'', b) => (s'',              stoi b      )) <$> decodeBytestring ⟨s'⟩
  | .some (s', 6, 3) => (λ (s'', b) => (s'', -(Int.ofNat (stoi b) - 1))) <$> decodeBytestring ⟨s'⟩
  | _                => .none

/-- Helper theorem: decodeInt consumes at least one byte on success -/
theorem decodeInt_consumes (s : String) :
  ∀ s' i, decodeInt s = some (s', i) → s'.data.length < s.data.length := by
  intro s' i h
  unfold decodeInt at h
  split at h
  · -- Case: decodeHead s.data = some (k, 0, n)
    rename_i k n hdh
    simp at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1]
    simp
    exact decodeHead_consumes s.data k 0 n hdh
  · -- Case: decodeHead s.data = some (k, 1, n)
    rename_i k n hdh
    simp at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1]
    simp
    exact decodeHead_consumes s.data k 1 n hdh
  · -- Case: decodeHead s.data = some (k, 6, 2), calls decodeBytestring
    rename_i k hdh
    cases h_db : decodeBytestring ⟨k⟩ with
    | none => simp [h_db] at h
    | some res =>
      simp [h_db] at h
      obtain ⟨h1, h2⟩ := h
      have h_head := decodeHead_consumes s.data k 6 2 hdh
      have h_bs := decodeBytestring_consumes ⟨k⟩ res.1 res.2 h_db
      simp at h_bs
      rw [← h1]
      simp
      omega
  · -- Case: decodeHead s.data = some (k, 6, 3), calls decodeBytestring
    rename_i k hdh
    cases h_db : decodeBytestring ⟨k⟩ with
    | none => simp [h_db] at h
    | some res =>
      simp [h_db] at h
      obtain ⟨h1, h2⟩ := h
      have h_head := decodeHead_consumes s.data k 6 3 hdh
      have h_bs := decodeBytestring_consumes ⟨k⟩ res.1 res.2 h_db
      simp at h_bs
      rw [← h1]
      simp
      omega
  · -- Case: decodeHead fails or other cases
    simp at h

/- Decodes a ctag from input `s`. -/
-- Spec B.7. D_ctag
def decodeCtag (s : List Char) : Option (List Char × Integer) :=
  match decodeHead s with
  | .some (s', 6, 102) => do
      let (s'', m, n) ← decodeHead s'
      if m = 4 ∧ n = 2
        then Prod.map String.data id <$> decodeInt ⟨s''⟩
        else .none
  | .some (s', 6, i) =>      if  121 ≤ i ∧ i ≤  127 then .some (s',  i -  121     )
                        else if 1280 ≤ i ∧ i ≤ 1400 then .some (s', (i - 1280) + 7)
                        else .none
  | _ => .none

/- Tries to decode a value from `s` using `f`. If fails it tries `g` with the same input. Fails if both fails. -/
def decodeAlternative {α β : Type} (f : List Char → Option (List Char × α)) (g : List Char → Option (List Char × β)) (s : List Char) : Option (List Char × (α ⊕ β)) :=
  match f s with
  | .some (s', a) => .some (s', .inl a)
  | .none         => (λ (s', b) => (s', .inr b)) <$> g s

/-- Helper theorem: decodeAlternative consumes at least one byte on success -/
theorem decodeAlternative_indef_head_consumes (s : List Char) :
  ∀ s' r, decodeAlternative decodeIndef decodeHead s = some (s', r) → s'.length < s.length := by
  intro s' r h
  unfold decodeAlternative at h
  split at h
  · rename_i s'' n hdi
    simp at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1]
    have := decodeIndef_consumes s s'' n hdi
    omega
  · simp [Option.map_eq_some_iff] at h
    obtain ⟨b, hdh, hb, heq_head, heq_pair⟩ := h
    obtain ⟨heq_s, heq_r⟩ := heq_pair
    rw [← heq_s]
    exact decodeHead_consumes s b hdh hb heq_head

/-- Helper theorem: decodeCtag consumes at least one byte on success -/
theorem decodeCtag_consumes (s : List Char) :
  ∀ s' i, decodeCtag s = some (s', i) → s'.length < s.length := by
  intro s' i h
  unfold decodeCtag at h
  split at h
  · -- Case: decodeHead s = some (k, 6, 102)
    rename_i k hdh
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s''', m, n⟩, hdh2, h_rest⟩ := h
    split at h_rest
    · -- decodeInt succeeds (split confirms m = 4 and n = 2)
      rename_i heq_mn
      cases h_int : decodeInt ⟨s'''⟩ with
      | none => simp [h_int] at h_rest
      | some res =>
        simp [h_int, Prod.map] at h_rest
        obtain ⟨h_eq_s', h_eq_i⟩ := h_rest
        have h_head1 := decodeHead_consumes s k 6 102 hdh
        -- Use heq_mn to show m = 4 and n = 2
        have ⟨hm, hn⟩ : m = 4 ∧ n = 2 := heq_mn
        subst hm hn
        have h_head2 := decodeHead_consumes k s''' 4 2 hdh2
        have h_int_cons := decodeInt_consumes ⟨s'''⟩ res.1 res.2 h_int
        simp at h_int_cons
        rw [← h_eq_s']
        simp
        omega
    · simp at h_rest
  · -- Case: decodeHead s = some (s'', 6, i_val) with i_val ≠ 102
    rename_i s'' i_val hne hdh
    split at h
    · simp at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1]
      exact decodeHead_consumes s s'' 6 i_val hdh
    · split at h
      · simp at h
        obtain ⟨h1, h2⟩ := h
        rw [← h1]
        exact decodeHead_consumes s s'' 6 i_val hdh
      · simp at h
  · -- Case: decodeHead fails or doesn't match pattern
    simp at h

-- Mutually recursive functions for decoding Data. These are defined at the top level
-- to allow explicit signatures and mutual termination proofs.
-- Note: These functions use `partial` because the mutual recursion termination proof
-- requires lemmas about byte consumption that create circular dependencies.
mutual
  -- Main decoder loop for Data values
  partial def decodeDataLoop (s : List Char) : Option (List Char × Data) :=
    match decodeAlternative decodeIndef decodeHead s with
    | .some (_ , .inl 2     ) => Prod.map String.data (.B ∘ ByteString.mk) <$> decodeBytestring ⟨s⟩
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

  -- Decode a fixed-length list of Data values
  partial def decodeList : Nat → List Char → Option (List Char × List Data)
    | .zero  , s => .some (s, [])
    | .succ p, s => match decodeDataLoop s with
        | some (s', d) => match decodeList p s' with
            | some (s'', l) => some (s'', d :: l)
            | none => none
        | none => none

  -- Decode an indefinite-length list of Data values
  partial def decodeListIndef : List Char → Option (List Char × List Data)
    | '\xFF' :: s' => .some (s', [])
    | s            => match decodeDataLoop s with
        | some (s', d) => match decodeListIndef s' with
            | some (s'', l) => some (s'', d :: l)
            | none => none
        | none => none

  -- Decode a fixed-length list of Data pairs (for Map)
  partial def decodePairList : Nat → List Char → Option (List Char × List (Data × Data))
    | .zero  , s => .some (s, [])
    | .succ p, s => match decodeDataLoop s with
        | some (s', k) => match decodeDataLoop s' with
            | some (s'', d) => match decodePairList p s'' with
                | some (s''', l) => some (s''', (k, d) :: l)
                | none => none
            | none => none
        | none => none

  -- Decode a constructor (Constr tag + list of Data values)
  partial def decodeConstr (s : List Char) : Option (List Char × Data) :=
    match decodeCtag s with
    | some (s', i) => match decodeAlternative decodeIndef decodeHead s' with
        | some (s'', r) => match r with
            | .inl 4      => Prod.map id (.Constr i) <$> decodeListIndef s''
            | .inr (4, n) => Prod.map id (.Constr i) <$> decodeList n s''
            | _           => .none
        | none => none
    | none => none
end

/- Decodes a builtin data from input `s`. -/
-- Spec B.7. D_data
def decodeData (s : String) : Option (String × Data) :=
  Prod.map String.mk id <$> decodeDataLoop s.data

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
