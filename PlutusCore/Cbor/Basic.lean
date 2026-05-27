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
def b_ (i n : Nat) : UInt8 := ((n / (256 ^ i)) % 256).toUInt8

/-- e_w: Returns the little-endian encoding of natural numbers in the prescribed width.
    In CBOR only the forms e₁ e₂ e₄ and e₈ are used. -/
-- Spec B.4. 𝖾_𝑘(𝑛) = [𝖻_(𝑘−1)(𝑛), … , 𝖻_0(𝑛)] if 𝑛 ≤ 256 ^ 𝑘 − 1.
@[simp] def e₁ (n : Nat) : ByteArray := ⟨#[b_ 0 n]⟩
@[simp] def e₂ (n : Nat) : ByteArray := ⟨#[b_ 1 n, b_ 0 n]⟩
@[simp] def e₄ (n : Nat) : ByteArray := ⟨#[b_ 3 n, b_ 2 n, b_ 1 n, b_ 0 n]⟩
@[simp] def e₈ (n : Nat) : ByteArray := ⟨#[b_ 7 n, b_ 6 n, b_ 5 n, b_ 4 n, b_ 3 n, b_ 2 n, b_ 1 n, b_ 0 n]⟩

/-- ε_head: Encodes the major type (`m`) × Nat pair -/
-- Spec B.4.
def encodeHead (m n : Nat) : Option ByteArray :=
  if m ≤ 7 then
         if n ≤                   23 then .some  ⟨#[(32 * m + n ).toUInt8]⟩
    else if n ≤                  255 then .some (⟨#[(32 * m + 24).toUInt8]⟩ ++ e₁ n)
    else if n ≤                65535 then .some (⟨#[(32 * m + 25).toUInt8]⟩ ++ e₂ n)
    else if n ≤           4294967295 then .some (⟨#[(32 * m + 26).toUInt8]⟩ ++ e₄ n)
    else if n ≤ 18446744073709551615 then .some (⟨#[(32 * m + 27).toUInt8]⟩ ++ e₈ n)
    else .none
  else .none

/-- Splitting a byte list into 64-byte chunks. -/
-- Spec B.5. "Canonical 64-byte decomposition"
def splitToChunks (b : ByteArray) : List ByteArray :=
  let length := b.size
  if length == 0
    then []
    else
      let chunksCount := ((length - 1) / 64) + 1
      (List.range chunksCount).map (λ ix =>
        b.extract (ix * 64) ((ix + 1) * 64)
      )

/-- Some sequences are encoded without a specified length (indefinite length encoding). -/
-- Spec B.4. Heads for indefinite-length items.
def encodeIndef (m : Nat) : ByteArray := ⟨#[(32 * m + 31).toUInt8]⟩

/-- Encodes a bytestring chunk. -/
-- Spec B.5. ε_B*
def encodeBytestringChunk (s : ByteArray) : Option ByteArray := do
  let length := s.size
  if length ≤ 256 ^ 8
    then .some ((←encodeHead 2 length) ++ s)
    else .none

/-- Encodes a bytestring.
    First splits the byte list into 64-byte chunks as detailed in the specification. -/
-- Spec B.5. ε_B*
def encodeBytestring (s : ByteArray) : Option ByteArray :=
  match splitToChunks s with
  | []      => encodeHead 2 0   -- empty bytestring is a definite 0-length string (0x40)
  | h :: [] => encodeBytestringChunk h
  | chunks  => do .some (encodeIndef 2
                 ++ (←(List.foldl ByteArray.append .empty) <$> (List.mapM id (encodeBytestringChunk <$> chunks))).push 0xFF)

/-- Encodes a natural number as a list of bytes in big-endian. -/
-- Spec B.6. itos
def itos (n : Nat) : ByteArray :=
  let rec loop (acc : ByteArray) (n : Nat) :=
    if h : n == 0
      then acc
      else loop (acc.push (n % 256).toUInt8) (n / 256)
  termination_by n
  decreasing_by
    apply Nat.div_lt_self
    · simp at h; omega
    · omega
  loop .empty n

/-- Encodes an integer using zigzag encoding. -/
-- Spec B.6. ε_Z
def encodeInt (n : Integer) : Option ByteArray :=
       if (                    0 ≤ n) && (n ≤  18446744073709551615) then encodeHead 0 (Int.toNat n)
  else if ( 18446744073709551616 ≤ n)                                then do return (←encodeHead 6 2) ++ (←encodeBytestring (itos (Int.toNat n)))
  else if (-18446744073709551616 ≤ n) && (n ≤                    -1) then encodeHead 1 ((-n - 1) |> Int.toNat)
  else if                                (n ≤ -18446744073709551617) then do return (←encodeHead 6 3) ++ (←encodeBytestring (itos (Int.toNat (-n - 1))))
  else .none

/-- Encodes a ctag. -/
-- Spec B.7. ε_ctag
def encodeCtag (i : Integer) : Option ByteArray :=
       if (0 ≤ i) && (i ≤   6) then encodeHead 6 ( 121 + i       |> Int.toNat)
  else if (7 ≤ i) && (i ≤ 127) then encodeHead 6 (1280 + (i - 7) |> Int.toNat)
  else do return (←encodeHead 6 102) ++ (←encodeHead 4 2) ++ (←encodeInt i)

/-- Converts a UPLC `ByteString` (which wraps a `String` of codepoint-as-byte
    chars) to its `ByteArray` representation. -/
@[inline] def byteStringToByteArray (bs : ByteString) : ByteArray :=
  (Char.toUInt8 <$> bs.data.data).toByteArray

/-- Encode data (builtinData). -/
-- Spec B.7. Encoding and  decoding Data. ε_data
def encodeData : Data → Option ByteArray
  | .Constr idx fields =>
      if fields.isEmpty then do
        -- empty field list is a DEFINITE empty array (0x80), matching the serialiseData builtin
        (←encodeCtag idx) ++ (←encodeHead 4 0)
      else do
        (←encodeCtag idx)
        ++ encodeIndef 4
        ++ (←List.foldlM (λ s a => do .some (s ++ (←encodeData a))) .empty fields)
        ++ ByteArray.mk #[0xFF]
  | .Map mxs => do
      (←encodeHead 5 mxs.length)
      ++ (←List.foldlM (λ s p => do .some (s ++ (←encodeData p.fst) ++ (←encodeData p.snd))) .empty mxs)
  | .List xs =>
      if xs.isEmpty then
        -- empty list is a DEFINITE empty array (0x80), matching the serialiseData builtin
        encodeHead 4 0
      else do
        encodeIndef 4
        ++ (←List.foldlM (λ s a => do .some (s ++ (←encodeData a))) .empty xs)
        ++ ByteArray.mk #[0xFF]
  | .I i  => encodeInt i
  | .B bs => encodeBytestring (byteStringToByteArray bs)

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

/-- A cursor into a `ByteArray`: the immutable input buffer plus the current read position. -/
structure DecodeState where
  input : ByteArray
  pos   : Nat
deriving DecidableEq

/-- Advances the cursor `n` bytes (default 1). -/
def DecodeState.advance (d : DecodeState) (n : Nat := 1) : DecodeState :=
  { d with pos := d.pos + n }

def DecodeState.nextUInt8 (d : DecodeState) (skip : Nat := 0) : Option UInt8 := d.input[d.pos + skip]?

@[simp] theorem DecodeState.advance_input (d : DecodeState) (n : Nat) :
    (d.advance n).input = d.input := rfl

@[simp] theorem DecodeState.advance_pos (d : DecodeState) (n : Nat) :
    (d.advance n).pos = d.pos + n := rfl

/-- Wrap a list of bytes into the UPLC `ByteString` domain value.
    `ByteString` is intentionally a wrapper around `String` (Haskell-compat),
    so a list of bytes is encoded by mapping each byte to the corresponding
    Char codepoint 0-255. -/
@[inline] def bytesToByteString (bs : List UInt8) : ByteString :=
  ⟨String.mk (Char.ofUInt8 <$> bs)⟩

/-- Wrap a `ByteArray` into the UPLC `ByteString` domain value. -/
@[inline] def byteArrayToByteString (b : ByteArray) : ByteString :=
  bytesToByteString b.toList

/-- Helper function that is used in reconstructing natural numbers from their big endian representation -/
def d_ (i : Nat) (c : UInt8) : Nat := c.toNat * (256 ^ i)

/-- Reading byte `i` from an array succeeds only when `i` is in bounds. -/
private theorem getElem?_some_lt {a : Array UInt8} {i : Nat} {b : UInt8} (h : a[i]? = some b) :
  i < a.size := by
    by_cases hlt : i < a.size
    · exact hlt
    · have hge : a.size ≤ i := Nat.le_of_not_lt hlt
      rw [Array.getElem?_eq_none hge] at h
      exact Option.noConfusion h

/-- Reading byte `i` from a `ByteArray` succeeds only when `i` is in bounds. -/
private theorem bytes_lt_of_byte {b : ByteArray} {i : Nat} {u : UInt8} (h : b.data[i]? = some u) :
  i < b.size := getElem?_some_lt h

/-- `d.nextUInt8 skip` succeeds only when `d.pos + skip` is in bounds. -/
private theorem DecodeState.nextUInt8_some_lt {d : DecodeState} {skip : Nat} {b : UInt8} (h : d.nextUInt8 skip = some b) :
  d.pos + skip < d.input.size := by
    have h' : d.input.data[d.pos + skip]? = some b := h
    exact bytes_lt_of_byte h'

-- Spec B.4. The `d_k` function is a general function to reconstruct a `k` byte natural number
-- from its big endian representation. In the spec only the forms with k = 1, 2, 4 and 8 are used.
/-- Decodes a one byte integer. -/
def d₁ (d : DecodeState) : Option (DecodeState × Nat) :=
  match d.nextUInt8 with
  | some b => .some (d.advance, b.toNat)
  | none   => .none

/-- Decodes a two byte integer. -/
def d₂ (d : DecodeState) : Option (DecodeState × Nat) := do
  let b₁ ← d.nextUInt8 0
  let b₀ ← d.nextUInt8 1
  some (d.advance 2, d_ 1 b₁ + d_ 0 b₀)

/-- Decodes a four byte integer. -/
def d₄ (d : DecodeState) : Option (DecodeState × Nat) := do
  let b₃ ← d.nextUInt8 0
  let b₂ ← d.nextUInt8 1
  let b₁ ← d.nextUInt8 2
  let b₀ ← d.nextUInt8 3
  some (d.advance 4, d_ 3 b₃ + d_ 2 b₂ + d_ 1 b₁ + d_ 0 b₀)

/-- Decodes an eight byte integer. -/
def d₈ (d : DecodeState) : Option (DecodeState × Nat) := do
  let b₇ ← d.nextUInt8 0
  let b₆ ← d.nextUInt8 1
  let b₅ ← d.nextUInt8 2
  let b₄ ← d.nextUInt8 3
  let b₃ ← d.nextUInt8 4
  let b₂ ← d.nextUInt8 5
  let b₁ ← d.nextUInt8 6
  let b₀ ← d.nextUInt8 7
  some (d.advance 8, d_ 7 b₇ + d_ 6 b₆ + d_ 5 b₅ + d_ 4 b₄ + d_ 3 b₃ + d_ 2 b₂ + d_ 1 b₁ + d_ 0 b₀)

/-- Decodes a "head" structure that describes how the next bytes should be interpreted. -/
-- Spec B.4. D_head
def decodeHead (d : DecodeState) : Option (DecodeState × Nat × Nat) :=
  match d.nextUInt8 with
  | none    => .none
  | some n' =>
      match n'.toNat % 32 with
      | 24 => (λ (d', k) => (d', n'.toNat / 32, k)) <$> d₁ d.advance
      | 25 => (λ (d', k) => (d', n'.toNat / 32, k)) <$> d₂ d.advance
      | 26 => (λ (d', k) => (d', n'.toNat / 32, k)) <$> d₄ d.advance
      | 27 => (λ (d', k) => (d', n'.toNat / 32, k)) <$> d₈ d.advance
      | m  => if m ≤ 23 then .some (d.advance, n'.toNat / 32, m) else .none

/-- Decodes a "head" structure with indefinite length that describes how the next bytes should be interpreted. -/
-- Spec B.4. D_indef
def decodeIndef (d : DecodeState) : Option (DecodeState × Nat) :=
  match d.nextUInt8 with
  | some n' =>
      let n := n'.toNat
      if n % 32 = 31 then .some (d.advance, n / 32) else .none
  | none    => .none

/-- Decodes (consumes) the next `n` bytes from the input. -/
-- Spec B.5. D_bytes
def decodeBytes (d : DecodeState) (n : Nat) : Option (DecodeState × ByteArray) :=
  if d.pos + n ≤ d.input.size
    then .some (d.advance n, d.input.extract d.pos (d.pos + n))
    else .none

/-- Decodes a definite length "block" (bytestring chunk). -/
-- Spec B.5. D_block
def decodeBlock (d : DecodeState) : Option (DecodeState × ByteArray) := do
  let (d', m, n) ← decodeHead d
  if m = 2 ∧ n ≤ 64
    then decodeBytes d' n
    else .none

-- ==========================
-- = Termination Helpers    =
-- ==========================

/-- `d₁` advances `pos` by exactly 1 on success. -/
theorem d₁_consumes (d : DecodeState) :
  ∀ d' k, d₁ d = some (d', k) → d'.input = d.input ∧ d'.pos = d.pos + 1 ∧ d'.pos ≤ d.input.size := by
    intro d' k h
    unfold d₁ at h
    split at h
    case h_1 b hget =>
      simp at h
      obtain ⟨h1, _⟩ := h
      subst h1
      have := DecodeState.nextUInt8_some_lt hget
      refine ⟨rfl, rfl, ?_⟩
      show d.pos + 1 ≤ d.input.size
      omega
    case h_2 => simp at h

/-- `d₂` advances `pos` by exactly 2 on success. -/
theorem d₂_consumes (d : DecodeState) :
  ∀ d' k, d₂ d = some (d', k) → d'.input = d.input ∧ d'.pos = d.pos + 2 ∧ d'.pos ≤ d.input.size := by
    intro d' k h
    unfold d₂ at h
    rcases hb1 : d.nextUInt8 with _ | b₁
    · simp [hb1] at h
    rcases hb0 : d.nextUInt8 1 with _ | b₀
    · simp [hb1, hb0] at h
    simp [hb1, hb0] at h
    obtain ⟨h1, _⟩ := h
    subst h1
    have := DecodeState.nextUInt8_some_lt hb0
    refine ⟨rfl, rfl, ?_⟩
    show d.pos + 2 ≤ d.input.size
    omega

/-- `d₄` advances `pos` by exactly 4 on success. -/
theorem d₄_consumes (d : DecodeState) :
  ∀ d' k, d₄ d = some (d', k) → d'.input = d.input ∧ d'.pos = d.pos + 4 ∧ d'.pos ≤ d.input.size := by
    intro d' k h
    unfold d₄ at h
    rcases hb3 : d.nextUInt8     with _ | b₃
    · simp [hb3] at h
    rcases hb2 : d.nextUInt8 1   with _ | b₂
    · simp [hb3, hb2] at h
    rcases hb1 : d.nextUInt8 2   with _ | b₁
    · simp [hb3, hb2, hb1] at h
    rcases hb0 : d.nextUInt8 3   with _ | b₀
    · simp [hb3, hb2, hb1, hb0] at h
    simp [hb3, hb2, hb1, hb0] at h
    obtain ⟨h1, _⟩ := h
    subst h1
    have := DecodeState.nextUInt8_some_lt hb0
    refine ⟨rfl, rfl, ?_⟩
    show d.pos + 4 ≤ d.input.size
    omega

/-- `d₈` advances `pos` by exactly 8 on success. -/
theorem d₈_consumes (d : DecodeState) :
  ∀ d' k, d₈ d = some (d', k) → d'.input = d.input ∧ d'.pos = d.pos + 8 ∧ d'.pos ≤ d.input.size := by
    intro d' k h
    unfold d₈ at h
    rcases hb7 : d.nextUInt8     with _ | b₇
    · simp [hb7] at h
    rcases hb6 : d.nextUInt8 1   with _ | b₆
    · simp [hb7, hb6] at h
    rcases hb5 : d.nextUInt8 2   with _ | b₅
    · simp [hb7, hb6, hb5] at h
    rcases hb4 : d.nextUInt8 3   with _ | b₄
    · simp [hb7, hb6, hb5, hb4] at h
    rcases hb3 : d.nextUInt8 4   with _ | b₃
    · simp [hb7, hb6, hb5, hb4, hb3] at h
    rcases hb2 : d.nextUInt8 5   with _ | b₂
    · simp [hb7, hb6, hb5, hb4, hb3, hb2] at h
    rcases hb1 : d.nextUInt8 6   with _ | b₁
    · simp [hb7, hb6, hb5, hb4, hb3, hb2, hb1] at h
    rcases hb0 : d.nextUInt8 7   with _ | b₀
    · simp [hb7, hb6, hb5, hb4, hb3, hb2, hb1, hb0] at h
    simp [hb7, hb6, hb5, hb4, hb3, hb2, hb1, hb0] at h
    obtain ⟨h1, _⟩ := h
    subst h1
    have := DecodeState.nextUInt8_some_lt hb0
    refine ⟨rfl, rfl, ?_⟩
    show d.pos + 8 ≤ d.input.size
    omega

/-- Helper for the four width-prefixed branches of `decodeHead`. -/
private theorem decodeHead_di_branch_consumes {d d' : DecodeState} {n' : UInt8} {dv k δ : Nat}
  {dx : DecodeState → Option (DecodeState × Nat)}
  (hdx_cons : ∀ d₀ k₀, dx d.advance = some (d₀, k₀) → d₀.input = (d.advance).input ∧ d₀.pos = (d.advance).pos + δ ∧ d₀.pos ≤ (d.advance).input.size)
  (h : (λ (p : DecodeState × Nat) => (p.1, n'.toNat / 32, p.2)) <$> dx d.advance = some (d', dv, k)) :
  d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
    rcases hdx : dx d.advance with _ | ⟨d_st, n_val⟩
    · rw [hdx] at h; simp at h
    rw [hdx] at h; simp at h
    obtain ⟨h_d', _, _⟩ := h
    have ⟨hin, hpos, hle⟩ := hdx_cons d_st n_val hdx
    simp at hin hpos hle
    subst h_d'
    refine ⟨hin, ?_, hle⟩
    omega

/-- `decodeHead` advances `pos` by at least 1 on success. -/
theorem decodeHead_consumes (d : DecodeState) :
  ∀ d' dv k, decodeHead d = some (d', dv, k) → d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
    intro d' dv k h
    unfold decodeHead at h
    rcases hget : d.nextUInt8 with _ | n'
    · simp only [hget] at h
      exact Option.noConfusion h
    simp only [hget] at h
    have hposlt : d.pos < d.input.size := by
      have := DecodeState.nextUInt8_some_lt hget
      omega
    split at h
    case h_1 _ => exact decodeHead_di_branch_consumes (d₁_consumes _) h
    case h_2 _ => exact decodeHead_di_branch_consumes (d₂_consumes _) h
    case h_3 _ => exact decodeHead_di_branch_consumes (d₄_consumes _) h
    case h_4 _ => exact decodeHead_di_branch_consumes (d₈_consumes _) h
    case h_5 m _ =>
      split at h
      · simp at h
        obtain ⟨h_d', _, _⟩ := h
        subst h_d'
        refine ⟨rfl, ?_, ?_⟩
        · show d.pos + 1 > d.pos; omega
        · show d.pos + 1 ≤ d.input.size; omega
      · simp at h

/-- `decodeIndef` advances `pos` by exactly 1 on success. -/
theorem decodeIndef_consumes (d : DecodeState) :
  ∀ d' n, decodeIndef d = some (d', n) → d'.input = d.input ∧ d'.pos = d.pos + 1 ∧ d'.pos ≤ d.input.size := by
    intro d' n h
    unfold decodeIndef at h
    rcases hb : d.nextUInt8 with _ | b
    · simp [hb] at h
    simp only [hb] at h
    split at h
    · simp at h
      obtain ⟨hd', _⟩ := h
      subst hd'
      have := DecodeState.nextUInt8_some_lt hb
      refine ⟨rfl, rfl, ?_⟩
      show d.pos + 1 ≤ d.input.size
      omega
    · simp at h

/-- `decodeBytes` advances `pos` by exactly `n` on success. -/
theorem decodeBytes_consumes (d : DecodeState) (n : Nat) :
  ∀ d' t, decodeBytes d n = some (d', t) → d'.input = d.input ∧ d'.pos = d.pos + n ∧ d'.pos ≤ d.input.size := by
    intro d' t h
    unfold decodeBytes at h
    split at h
    · simp at h
      obtain ⟨h1, _⟩ := h
      subst h1
      refine ⟨rfl, rfl, ?_⟩
      show d.pos + n ≤ d.input.size
      assumption
    · simp at h

/-- `decodeBlock` advances `pos` by at least 1 on success. -/
theorem decodeBlock_consumes (d : DecodeState) :
  ∀ d' t, decodeBlock d = some (d', t) → d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
    intro d' t h
    unfold decodeBlock at h
    cases hdh : decodeHead d with
    | none => simp [hdh] at h
    | some res =>
      obtain ⟨d'', m, n⟩ := res
      simp [hdh] at h
      obtain ⟨_, hbytes⟩ := h
      have ⟨h1, h2, h3⟩ := decodeHead_consumes d d'' m n hdh
      have ⟨h4, h5, h6⟩ := decodeBytes_consumes d'' n d' t hbytes
      refine ⟨?_, ?_, ?_⟩
      · rw [h4, h1]
      · rw [h5]; omega
      · rw [h1] at h6; exact h6

set_option linter.unusedVariables false in
/-- Inner loop accumulating bytestring chunks until the `0xFF` terminator. -/
def decodeBlocksLoop (acc : ByteArray) (d : DecodeState) : Option (DecodeState × ByteArray) :=
  if d.nextUInt8 = some 0xFF then
    .some (d.advance, acc)
  else
    match h : decodeBlock d with
    | some (d', t) => decodeBlocksLoop (acc ++ t) d'
    | none         => none
  termination_by d.input.size - d.pos
  decreasing_by
    simp_wf
    have ⟨hin, hgt, hle⟩ := decodeBlock_consumes d d' t h
    rw [hin]
    omega

/-- Decodes an indefinite number of blocks. -/
-- Spec B.5. D_blocks
def decodeBlocks : DecodeState → Option (DecodeState × ByteArray) := decodeBlocksLoop .empty

/-- `decodeBlocksLoop` advances `pos` by at least 1 on success (inducted over a fuel bound). -/
theorem decodeBlocksLoop_consumes :
  ∀ (n : Nat) (acc : ByteArray) (d d' : DecodeState) (t : ByteArray),
    d.input.size - d.pos ≤ n → decodeBlocksLoop acc d = some (d', t) →
    d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
      intro n
      induction n with
      | zero =>
        intro acc d d' t hbound h
        unfold decodeBlocksLoop at h
        split at h
        · -- 0xFF terminator: needs d.pos < d.input.size, contradicted by hbound
          rename_i h_ff
          have hposlt := DecodeState.nextUInt8_some_lt h_ff
          simp at hposlt
          omega
        · split at h
          · rename_i d'' t' hdb
            have ⟨_, hgt, _⟩ := decodeBlock_consumes d d'' t' hdb
            omega
          · contradiction
      | succ n' ih =>
        intro acc d d' t hbound h
        unfold decodeBlocksLoop at h
        split at h
        · -- 0xFF terminator branch
          rename_i h_ff
          have hposlt := DecodeState.nextUInt8_some_lt h_ff
          simp at hposlt
          simp at h
          obtain ⟨h1, _⟩ := h
          subst h1
          refine ⟨rfl, ?_, ?_⟩
          · simp
          · show d.pos + 1 ≤ d.input.size; omega
        · split at h
          · -- decodeBlock succeeds, recurse
            rename_i d'' t' hdb
            have ⟨hbin, hbgt, hble⟩ := decodeBlock_consumes d d'' t' hdb
            have hbound' : d''.input.size - d''.pos ≤ n' := by
              rw [hbin]; omega
            have ⟨hrin, hrgt, hrle⟩ := ih (acc ++ t') d'' d' t hbound' h
            refine ⟨?_, ?_, ?_⟩
            · rw [hrin, hbin]
            · omega
            · rw [hbin] at hrle; exact hrle
          · contradiction

/-- `decodeBlocks` advances `pos` by at least 1 on success. -/
theorem decodeBlocks_consumes :
  ∀ d d' t, decodeBlocks d = some (d', t) →
    d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
      intro d d' t h
      unfold decodeBlocks at h
      exact decodeBlocksLoop_consumes (d.input.size - d.pos) .empty d d' t (Nat.le_refl _) h

/-- Decodes a bytestring from a `DecodeState` (internal). -/
def decodeBytestringL (d : DecodeState) : Option (DecodeState × ByteArray) :=
  match decodeBlock d with
  | .some res => .some res
  | .none     => do
      let (d', n) ← decodeIndef d
      if n = 2
        then decodeBlocks d'
        else .none

/-- `decodeBytestringL` advances `pos` by at least 1 on success. -/
theorem decodeBytestringL_consumes (d : DecodeState) :
  ∀ d' t, decodeBytestringL d = some (d', t) →
    d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
      intro d' t h
      unfold decodeBytestringL at h
      cases hdb : decodeBlock d with
      | some pair =>
        obtain ⟨d'', t'⟩ := pair
        rw [hdb] at h
        simp at h
        obtain ⟨hd_eq, _⟩ := h
        subst hd_eq
        exact decodeBlock_consumes d d'' t' hdb
      | none =>
        rw [hdb] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨d'', n⟩, hdi, hrest⟩ := h
        split at hrest
        · cases hblocks : decodeBlocks d'' with
          | none => simp [hblocks] at hrest
          | some res =>
            rcases res with ⟨ra, rb⟩
            simp [hblocks] at hrest
            obtain ⟨heqs, _⟩ := hrest
            have ⟨h1, h2, h3⟩ := decodeIndef_consumes d d'' n hdi
            have ⟨h4, h5, h6⟩ := decodeBlocks_consumes d'' ra rb hblocks
            subst heqs
            refine ⟨?_, ?_, ?_⟩
            · rw [h4, h1]
            · omega
            · rw [h1] at h6; exact h6
        · simp at hrest

/-- Decodes a bytestring from the input `b`. -/
-- Spec B.5. D_B*
def decodeBytestring (b : ByteArray) : Option (ByteArray × ByteArray) :=
  (decodeBytestringL { input := b, pos := 0 }).map (λ (d', t) =>
    (d'.input.extract d'.pos d'.input.size, t))

/-- Decodes a "large" block, which can have a length larger than 64 bytes. -/
def decodeLargeBlock (d : DecodeState) : Option (DecodeState × ByteArray) := do
  let (d', m, n) ← decodeHead d
  if m = 2
    then decodeBytes d' n
    else .none

/-- `decodeLargeBlock` advances `pos` by at least 1 on success. -/
theorem decodeLargeBlock_consumes (d : DecodeState) :
  ∀ d' t, decodeLargeBlock d = some (d', t) →
    d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
      intro d' t h
      unfold decodeLargeBlock at h
      cases hdh : decodeHead d with
      | none => simp [hdh] at h
      | some res =>
        obtain ⟨d'', m, n⟩ := res
        simp [hdh] at h
        obtain ⟨_, hbytes⟩ := h
        have ⟨h1, h2, h3⟩ := decodeHead_consumes d d'' m n hdh
        have ⟨h4, h5, h6⟩ := decodeBytes_consumes d'' n d' t hbytes
        refine ⟨?_, ?_, ?_⟩
        · rw [h4, h1]
        · rw [h5]; omega
        · rw [h1] at h6; exact h6

set_option linter.unusedVariables false in
def decodeLargeBlocksLoop (acc : ByteArray) (d : DecodeState) : Option (DecodeState × ByteArray) :=
  if d.nextUInt8 = some 0xFF then
    .some (d.advance, acc)
  else
    match h : decodeLargeBlock d with
    | some (d', t) => decodeLargeBlocksLoop (acc ++ t) d'
    | none         => none
  termination_by d.input.size - d.pos
  decreasing_by
    simp_wf
    have ⟨hin, hgt, hle⟩ := decodeLargeBlock_consumes d d' t h
    rw [hin]
    omega

/-- Decodes a sequence of "large" blocks. -/
def decodeLargeBlocks : DecodeState → Option (DecodeState × ByteArray) := decodeLargeBlocksLoop .empty

/-- `decodeLargeBlocksLoop` advances `pos` by at least 1 on success. -/
theorem decodeLargeBlocksLoop_consumes :
  ∀ (n : Nat) (acc : ByteArray) (d d' : DecodeState) (t : ByteArray),
    d.input.size - d.pos ≤ n → decodeLargeBlocksLoop acc d = some (d', t) →
      d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
        intro n
        induction n with
        | zero =>
          intro acc d d' t hbound h
          unfold decodeLargeBlocksLoop at h
          split at h
          · rename_i h_ff
            have hposlt := DecodeState.nextUInt8_some_lt h_ff
            simp at hposlt
            omega
          · split at h
            · rename_i d'' t' hdb
              have ⟨_, hgt, _⟩ := decodeLargeBlock_consumes d d'' t' hdb
              omega
            · contradiction
        | succ n' ih =>
          intro acc d d' t hbound h
          unfold decodeLargeBlocksLoop at h
          split at h
          · rename_i h_ff
            have hposlt := DecodeState.nextUInt8_some_lt h_ff
            simp at hposlt
            simp at h
            obtain ⟨h1, _⟩ := h
            subst h1
            refine ⟨rfl, ?_, ?_⟩
            · simp
            · show d.pos + 1 ≤ d.input.size; omega
          · split at h
            · rename_i d'' t' hdb
              have ⟨hbin, hbgt, hble⟩ := decodeLargeBlock_consumes d d'' t' hdb
              have hbound' : d''.input.size - d''.pos ≤ n' := by
                rw [hbin]; omega
              have ⟨hrin, hrgt, hrle⟩ := ih (acc ++ t') d'' d' t hbound' h
              refine ⟨?_, ?_, ?_⟩
              · rw [hrin, hbin]
              · omega
              · rw [hbin] at hrle; exact hrle
            · contradiction

/-- `decodeLargeBlocks` advances `pos` by at least 1 on success. -/
theorem decodeLargeBlocks_consumes :
  ∀ d d' t, decodeLargeBlocks d = some (d', t) →
    d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
      intro d d' t h
      unfold decodeLargeBlocks at h
      exact decodeLargeBlocksLoop_consumes (d.input.size - d.pos) .empty d d' t (Nat.le_refl _) h

/-- Decodes a "large" bytestring from a `DecodeState` (internal). -/
def decodeLargeBytestringL (d : DecodeState) : Option (DecodeState × ByteArray) :=
  match decodeLargeBlock d with
  | .some res => .some res
  | .none     => do
      let (d', n) ← decodeIndef d
      if n = 2
        then decodeLargeBlocks d'
        else .none

/-- Decodes a "large" bytestring from a `ByteArray`. -/
def decodeLargeBytestring (b : ByteArray) : Option (ByteArray × ByteArray) :=
  (decodeLargeBytestringL { input := b, pos := 0 }).map (λ (d', t) =>
    (d'.input.extract d'.pos d'.input.size, t))

/-- Reconstructs a natural number from its big endian representation. -/
-- Spec B.6. stoi
def stoi (b : ByteArray) : Nat := b.foldl (λ acc x => acc * 256 + x.toNat) 0

/-- Decodes an integer value from a `DecodeState` (internal). -/
def decodeIntL (d : DecodeState) : Option (DecodeState × Integer) :=
  match decodeHead d with
  | .some (d', 0, n) => .some (d',  (Int.ofNat n)    )
  | .some (d', 1, n) => .some (d', -(Int.ofNat n) - 1)
  | .some (d', 6, 2) => (λ (d'', b) => (d'',              stoi b      )) <$> decodeBytestringL d'
  | .some (d', 6, 3) => (λ (d'', b) => (d'', -(Int.ofNat (stoi b)) - 1)) <$> decodeBytestringL d'
  | _                => .none

/-- `decodeIntL` advances `pos` by at least 1 on success. -/
theorem decodeIntL_consumes (d : DecodeState) :
  ∀ d' i, decodeIntL d = some (d', i) →
    d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
      intro d' i h
      unfold decodeIntL at h
      split at h
      · -- (d'', 0, n)
        rename_i d'' n hdh
        simp at h
        obtain ⟨h1, _⟩ := h
        subst h1
        exact decodeHead_consumes d d'' 0 n hdh
      · rename_i d'' n hdh
        simp at h
        obtain ⟨h1, _⟩ := h
        subst h1
        exact decodeHead_consumes d d'' 1 n hdh
      · rename_i d'' hdh
        cases hbs : decodeBytestringL d'' with
        | none => simp [hbs] at h
        | some res =>
          simp [hbs] at h
          obtain ⟨h1, _⟩ := h
          have ⟨h2, h3, h4⟩ := decodeHead_consumes d d'' 6 2 hdh
          have ⟨h5, h6, h7⟩ := decodeBytestringL_consumes d'' res.1 res.2 hbs
          subst h1
          refine ⟨?_, ?_, ?_⟩
          · rw [h5, h2]
          · omega
          · rw [h2] at h7; exact h7
      · rename_i d'' hdh
        cases hbs : decodeBytestringL d'' with
        | none => simp [hbs] at h
        | some res =>
          simp [hbs] at h
          obtain ⟨h1, _⟩ := h
          have ⟨h2, h3, h4⟩ := decodeHead_consumes d d'' 6 3 hdh
          have ⟨h5, h6, h7⟩ := decodeBytestringL_consumes d'' res.1 res.2 hbs
          subst h1
          refine ⟨?_, ?_, ?_⟩
          · rw [h5, h2]
          · omega
          · rw [h2] at h7; exact h7
      · simp at h

/-- Decodes an integer value from a `ByteArray`. -/
--  Spec B.6. D_Z
def decodeInt (b : ByteArray) : Option (ByteArray × Integer) :=
  (decodeIntL { input := b, pos := 0 }).map (λ (d', i) =>
    (d'.input.extract d'.pos d'.input.size, i))

/-- Decodes a ctag from a `DecodeState`. -/
-- Spec B.7. D_ctag
def decodeCtag (d : DecodeState) : Option (DecodeState × Integer) :=
  match decodeHead d with
  | .some (d', 6, 102) => do
      -- The definite 2-element wrapper (0x82) is accepted here. The indefinite form
      -- (0x9f..0xff) that Data.hs also accepts is handled by decodeIndefConstr.
      let (d'', m, n) ← decodeHead d'
      if m = 4 ∧ n = 2
        then do
          -- Index is a direct Word64 (matches decodeWord64). A negative or bignum-encoded
          -- index is write-only, so reject it on decode.
          let (d''', im, iv) ← decodeHead d''
          if im = 0 then .some (d''', Int.ofNat iv) else .none
        else
          .none
  | .some (d', 6, i) =>      if  121 ≤ i ∧ i ≤  127 then .some (d',  i -  121     )
                        else if 1280 ≤ i ∧ i ≤ 1400 then .some (d', (i - 1280) + 7)
                        else .none
  | _ => .none

/-- Tries to decode using `f`; on failure, tries `g`. -/
def decodeAlternative {α β : Type}
    (f : DecodeState → Option (DecodeState × α))
    (g : DecodeState → Option (DecodeState × β))
    (d : DecodeState) : Option (DecodeState × (α ⊕ β)) :=
  match f d with
  | .some (d', a) => .some (d', .inl a)
  | .none         => (λ (d', b) => (d', .inr b)) <$> g d

/-- `decodeAlternative decodeIndef decodeHead` advances `pos` by at least 1 on success. -/
theorem decodeAlternative_indef_head_consumes (d : DecodeState) :
  ∀ d' r, decodeAlternative decodeIndef decodeHead d = some (d', r) →
    d'.input = d.input ∧ d'.pos > d.pos ∧ d'.pos ≤ d.input.size := by
      intro d' r h
      unfold decodeAlternative at h
      split at h
      · rename_i d'' n hdi
        simp at h
        obtain ⟨h1, _⟩ := h
        subst h1
        have ⟨h2, h3, h4⟩ := decodeIndef_consumes d d'' n hdi
        refine ⟨h2, ?_, h4⟩
        rw [h3]; omega
      · cases hdh : decodeHead d with
        | none => rw [hdh] at h; simp at h
        | some triple =>
          obtain ⟨d'', b, c⟩ := triple
          rw [hdh] at h
          simp at h
          obtain ⟨h_eq, _⟩ := h
          subst h_eq
          exact decodeHead_consumes d d'' b c hdh

/-- `decodeCtag` advances `pos` by at least 1 on success. -/
theorem decodeCtag_consumes (d : DecodeState) :
  ∀ df i, decodeCtag d = some (df, i) →
    df.input = d.input ∧ df.pos > d.pos ∧ df.pos ≤ d.input.size := by
      intro dF iF h
      unfold decodeCtag at h
      match hdd : decodeHead d with
      | some (d', j, i) =>
          if hj : j = 6
            then
              subst hj
              simp [hdd, Option.bind] at h
              if hi : i = 102 then
                subst hi
                match hdd' : decodeHead d' with
                | some (d'', m, n) =>
                    simp [hdd'] at h
                    obtain ⟨hmn, h⟩ := h
                    obtain ⟨hm, hn⟩ := hmn
                    subst hm hn
                    match hdd'' : decodeHead d'' with
                    | some (d''', im, iv) =>
                        simp [hdd''] at h
                        have ⟨h1, h2, h3⟩ := decodeHead_consumes d   d'    6 102 hdd
                        have ⟨h4, h5, h6⟩ := decodeHead_consumes d'  d''   4   2 hdd'
                        have ⟨h7, h8, h9⟩ := decodeHead_consumes d'' d''' im  iv hdd''
                        have ⟨h10, h11, h12⟩ := h
                        have hf1 : dF.input = d.input      := by grind
                        have hf2 :   dF.pos > d.pos        := by grind
                        have hf3 :   dF.pos ≤ d.input.size := by grind
                        grind
                    | none =>
                        simp [hdd''] at h
                | none =>
                    simp [hdd'] at h
              else
                simp at h
                if hi : 121 ≤ i ∧ i ≤ 127
                  then
                    simp [hi] at h
                    obtain ⟨h, _⟩ := h
                    subst h
                    have ⟨h1, h2, h3⟩ := decodeHead_consumes d d' 6 i hdd
                    grind
                  else
                    simp [hi] at h
                    obtain ⟨_, h, _⟩ := h
                    subst h
                    have ⟨h1, h2, h3⟩ := decodeHead_consumes d d' 6 i hdd
                    grind
          else
            simp [hdd, hj] at h
      | none =>
          simp [hdd] at h

-- Mutually recursive functions for decoding Data. These are defined at the top level
-- to allow explicit signatures and mutual termination proofs.
-- Note: These functions use `partial` because the mutual recursion termination proof
-- requires lemmas about byte consumption that create circular dependencies.
mutual
  -- Main decoder loop for Data values
  partial def decodeDataLoop (d : DecodeState) : Option (DecodeState × Data) :=
    match decodeAlternative decodeIndef decodeHead d with
    | .some (_ , .inl 2     ) => Prod.map id (.B ∘ byteArrayToByteString) <$> decodeBytestringL d
    | .some (d', .inl 4     ) => Prod.map id .List                        <$> decodeListIndef d'
    | .some (d', .inl 5     ) => Prod.map id .Map                         <$> decodePairListIndef d'
    | .some (_ , .inr (0, _))
    | .some (_ , .inr (1, _))
    | .some (_ , .inr (6, 2))
    | .some (_ , .inr (6, 3)) => Prod.map id .I                           <$> decodeIntL d
    | .some (_ , .inr (2, _)) => Prod.map id (.B ∘ byteArrayToByteString) <$> decodeBytestringL d
    | .some (d', .inr (4, n)) => Prod.map id .List                        <$> decodeList n d'
    | .some (d', .inr (5, n)) => Prod.map id .Map                         <$> decodePairList n d'
    | .some (_ , .inr (6, _)) =>                                              decodeConstr d
    | _ => .none

  -- Decode a fixed-length list of Data values
  partial def decodeList : Nat → DecodeState → Option (DecodeState × List Data)
    | .zero  , d => .some (d, [])
    | .succ p, d => do
        let (d' , x) ← decodeDataLoop d
        let (d'', l) ← decodeList p d'
        return (d'', x :: l)

  -- Decode an indefinite-length list of Data values
  partial def decodeListIndef (d : DecodeState) : Option (DecodeState × List Data) :=
    match d.nextUInt8 with
    | some 0xFF => .some (d.advance, [])
    | _ => do
        let (d' , x) ← decodeDataLoop d
        let (d'', l) ← decodeListIndef d'
        return (d'', x :: l)

  -- Decode a fixed-length list of Data pairs (for Map)
  partial def decodePairList : Nat → DecodeState → Option (DecodeState × List (Data × Data))
    | .zero  , d => .some (d, [])
    | .succ p, d => do
        let (d'  , k) ← decodeDataLoop d
        let (d'' , v) ← decodeDataLoop d'
        let (d''', l) ← decodePairList p d''
        return (d''', (k, v) :: l)

  -- Decode an indefinite-length list of Data pairs (an indefinite-length Map, 0xbf..0xff). Spec B.7
  -- D_data decodes maps as definite-only, so this EXTENDS the decoder beyond the spec to the
  -- indefinite form Data.hs also accepts (decodeMapLenOrIndef). Decode-only, the encoder still
  -- emits only definite maps.
  partial def decodePairListIndef (d : DecodeState) : Option (DecodeState × List (Data × Data)) :=
    match d.nextUInt8 with
    | some 0xFF => .some (d.advance, [])
    | _ => do
        let (d'  , k) ← decodeDataLoop d
        let (d'' , v) ← decodeDataLoop d'
        let (d''', l) ← decodePairListIndef d''
        return (d''', (k, v) :: l)

  -- Decode a constructor whose tag-102 wrapper uses the INDEFINITE 2-element array
  -- (0x9f index args 0xff), the form Data.hs accepts via decodeListLenOrIndef. The canonical
  -- encoder never emits it, so this is decode-only leniency toward the reference implementation.
  partial def decodeIndefConstr (d : DecodeState) : Option (DecodeState × Data) := do
    let (d', m, n) ← decodeHead d
    guard (m = 6 ∧ n = 102)
    let (d'', n)   ← decodeIndef d'
    guard (n = 4)
    let (d''', n, iv) ← decodeHead d''
    guard (n = 0)
    let (d4, alt) ← decodeAlternative decodeIndef decodeHead d'''
    match alt with
    | .inl 4 =>
        let (di, args) ← decodeListIndef d4
        let f          ← di.nextUInt8
        guard (f = 0xFF)
        return (di.advance, .Constr (Int.ofNat iv) args)
    | .inr (4, n) =>
        let (dd, args) ← decodeList n d4
        let f          ← dd.nextUInt8
        guard (f = 0xFF)
        return (dd.advance, .Constr (Int.ofNat iv) args)
    | _ => none

  -- Decode a constructor (Constr tag + list of Data values)
  partial def decodeConstr (d : DecodeState) : Option (DecodeState × Data) :=
    match decodeCtag d with
    | some (d', i) => do
        let (d'', r) ← decodeAlternative decodeIndef decodeHead d'
        match r with
            | .inl 4      => Prod.map id (.Constr i) <$> decodeListIndef d''
            | .inr (4, n) => Prod.map id (.Constr i) <$> decodeList n d''
            | _           => .none
    | none => decodeIndefConstr d
end

/- Decodes a builtin data from input `b`. -/
-- Spec B.7. D_data, EXTENDED beyond the spec on two indefinite-length forms the spec rejects but
-- Data.hs accepts: indefinite maps (decodePairListIndef) and the indefinite tag-102 constructor
-- wrapper (decodeIndefConstr). Decode-only, the encoder is unchanged.
def decodeData (b : ByteArray) : Option (ByteArray × Data) :=
  (decodeDataLoop { input := b, pos := 0 }).map (λ (d', x) =>
    (d'.input.extract d'.pos d'.input.size, x))

end CborInternal

export CborInternal
  ( -- encoding
    encodeBytestring
    encodeInt
    encodeData
    -- decoding
    bytesToByteString
    byteArrayToByteString
    decodeBytestring
    decodeLargeBytestring
    decodeInt
    decodeData
  )

end PlutusCore.Cbor
