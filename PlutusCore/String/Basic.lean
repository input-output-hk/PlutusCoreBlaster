import PlutusCore.ByteString.Basic

namespace PlutusCore.String
open PlutusCore.ByteString
open PlutusCore.Bytes (byteStr uncons cpStr uncons_cons uncons_nil)

/-! ## Formalisation for PlutusCore String representation and builtin functions. -/

namespace PlutusCore.StringInternal

-- We here use the Lean4 String representation

/-! ## Builtin String functions. -/

/-- Return an empty String -/
def emptyString : String := ""

/-- Given two Strings `[u₁, ..., uₘ]` and `[v₁, ..., vₙ]` return `[u₁, ..., uₘ, v₁, ..., vₙ]` -/
def appendString (s1 : String) (s2 : String) : String := s1 ++ s2

def equalsString (s1 : String) (s2 : String) : Bool := s1 == s2

def utf8EncodeChar (c : Char) : List Char :=
  let v := c.val
  if v ≤ 0x7f then
    [c]
  else if v ≤ 0x7ff then
    [Char.ofUInt8 ((v >>>  6).toUInt8 &&& 0x1f ||| 0xc0),
     Char.ofUInt8 (v.toUInt8 &&& 0x3f ||| 0x80)]
  else if v ≤ 0xffff then
    [Char.ofUInt8 ((v >>> 12).toUInt8 &&& 0x0f ||| 0xe0),
     Char.ofUInt8 ((v >>>  6).toUInt8 &&& 0x3f ||| 0x80),
     Char.ofUInt8 (v.toUInt8 &&& 0x3f ||| 0x80)]
  else
    [Char.ofUInt8 ((v >>> 18).toUInt8 &&& 0x07 ||| 0xf0),
     Char.ofUInt8 ((v >>> 12).toUInt8 &&& 0x3f ||| 0x80),
     Char.ofUInt8 ((v >>>  6).toUInt8 &&& 0x3f ||| 0x80),
     Char.ofUInt8 (v.toUInt8 &&& 0x3f ||| 0x80)]

/-- The UTF-8 encoding of the code point `c` (a Unicode scalar value), as `utf8EncodeChar`
    computes it, but built from `byteStr` so that Blaster can translate it for a symbolic `c`. -/
def utf8EncodeCode (c : Nat) : String :=
  if c ≤ 0x7f then
    byteStr c
  else if c ≤ 0x7ff then
    byteStr (0xc0 + c / 0x40) ++
    byteStr (0x80 + c % 0x40)
  else if c ≤ 0xffff then
    byteStr (0xe0 + c / 0x1000) ++
    byteStr (0x80 + c / 0x40 % 0x40) ++
    byteStr (0x80 + c % 0x40)
  else
    byteStr (0xf0 + c / 0x40000) ++
    byteStr (0x80 + c / 0x1000 % 0x40) ++
    byteStr (0x80 + c / 0x40 % 0x40) ++
    byteStr (0x80 + c % 0x40)

/-- Coverts String to ByteString using utf8 encoding.
    Reads characters with `uncons`, so Blaster can translate it for a symbolic string. -/
def encodeUtf8 (s : String) : ByteString := ⟨loop s.length s⟩
where
  /-- Encodes (at most `n` characters of) `s`. -/
  loop : Nat → String → String
    | 0    , _ => ""
    | n + 1, s =>
      match uncons s with
      | none        => ""
      | some (c, t) => utf8EncodeCode c ++ loop n t

/-- `acc ++ encodeUtf8.loop n ⟨l⟩`, tail recursively, for compiled code. `encodeUtf8.loop` reads
    with `uncons`, which copies the rest of the string, and takes a stack frame per character. -/
def encodeUtf8Go : Nat → List Char → String → String
  | 0    , _      , acc => acc
  | _ + 1, []     , acc => acc
  | n + 1, c :: cs, acc => encodeUtf8Go n cs (acc ++ utf8EncodeCode c.toNat)

theorem encodeUtf8Go_eq (n : Nat) (l : List Char) (acc : String) :
    encodeUtf8Go n l acc = acc ++ encodeUtf8.loop n ⟨l⟩ := by
  induction n generalizing l acc with
  | zero => rw [encodeUtf8Go, encodeUtf8.loop, String.append_empty]
  | succ n ih =>
    cases l with
    | nil => rw [encodeUtf8Go, encodeUtf8.loop, uncons_nil, String.append_empty]
    | cons c cs => rw [encodeUtf8Go, encodeUtf8.loop, uncons_cons, ih, String.append_assoc]

def encodeUtf8Impl (s : String) : ByteString := ⟨encodeUtf8Go s.length s.data ""⟩

/-- Compiled code runs `encodeUtf8Impl` for `encodeUtf8`. -/
@[csimp] theorem encodeUtf8_eq_impl : @encodeUtf8 = @encodeUtf8Impl := by
  funext s; rw [encodeUtf8, encodeUtf8Impl, encodeUtf8Go_eq, String.empty_append]

def utf8DecodeChar? (a : List Char) (i : Nat) : Option Char := do
  let u ← a[i]?
  let c := u.toUInt8
  if c &&& 0x80 == 0 then
    some ⟨c.toUInt32, .inl (Nat.lt_trans c.toBitVec.isLt (by decide))⟩
  else if c &&& 0xe0 == 0xc0 then
    let u1 ← a[i+1]?
    let c1 := u1.toUInt8
    guard (c1 &&& 0xc0 == 0x80)
    let r := ((c &&& 0x1f).toUInt32 <<< 6) ||| (c1 &&& 0x3f).toUInt32
    guard (0x80 ≤ r)
    -- TODO: Prove h from the definition of r once we have the necessary lemmas
    if h : r < 0xd800 then some ⟨r, .inl ((UInt32.lt_ofNat_iff (by decide)).1 h)⟩ else none
  else if c &&& 0xf0 == 0xe0 then
    let u1 ← a[i+1]?
    let u2 ← a[i+2]?
    let c1 := u1.toUInt8
    let c2 := u2.toUInt8
    guard (c1 &&& 0xc0 == 0x80 && c2 &&& 0xc0 == 0x80)
    let r :=
      ((c &&& 0x0f).toUInt32 <<< 12) |||
      ((c1 &&& 0x3f).toUInt32 <<< 6) |||
      (c2 &&& 0x3f).toUInt32
    guard (0x800 ≤ r)
    -- TODO: Prove `r < 0x110000` from the definition of r once we have the necessary lemmas
    if h : r < 0xd800 ∨ 0xdfff < r ∧ r < 0x110000 then
      have :=
        match h with
        | .inl h => Or.inl ((UInt32.lt_ofNat_iff (by decide)).1 h)
        | .inr h => Or.inr ⟨(UInt32.ofNat_lt_iff (by decide)).1 h.left, (UInt32.lt_ofNat_iff (by decide)).1 h.right⟩
      some ⟨r, this⟩
    else
      none
  else if c &&& 0xf8 == 0xf0 then
    let u1 ← a[i+1]?
    let u2 ← a[i+2]?
    let u3 ← a[i+3]?
    let c1 := u1.toUInt8
    let c2 := u2.toUInt8
    let c3 := u3.toUInt8
    guard (c1 &&& 0xc0 == 0x80 && c2 &&& 0xc0 == 0x80 && c3 &&& 0xc0 == 0x80)
    let r :=
      ((c &&& 0x07).toUInt32 <<< 18) |||
      ((c1 &&& 0x3f).toUInt32 <<< 12) |||
      ((c2 &&& 0x3f).toUInt32 <<< 6) |||
      (c3 &&& 0x3f).toUInt32
    if h : 0x10000 ≤ r ∧ r < 0x110000 then
      some ⟨r, .inr ⟨Nat.lt_of_lt_of_le (by decide) ((UInt32.ofNat_le_iff (by decide)).1 h.left), (UInt32.lt_ofNat_iff (by decide)).1 h.right⟩⟩
    else none
  else
    none

/-- Decodes a ByteString to String using utf8 decoding.
    An error is triggered when the ByteString is not uft8 encoded.

    Accepts and rejects exactly what `utf8DecodeChar?` does, byte for byte, including reading each
    character of `bs` modulo 256. Reads bytes with `uncons` and writes characters with `cpStr`, so
    Blaster can translate it for a symbolic byte string.
-/
def decodeUtf8 (bs : ByteString) : Except String String :=
  loop bs.length bs.data ""
where
  invalid : Except String String := throw "decodeUtf8: invalid ByteString"
  /-- Whether `b` is a continuation byte, `0b10xxxxxx`. -/
  cont (b : Nat) : Bool := b / 0x40 == 2
  /-- Decodes (at most `n` characters of) `s` onto `acc`. -/
  loop : Nat → String → String → Except String String
    | 0    , _, acc => pure acc
    | n + 1, s, acc =>
      match uncons s with
      | none          => pure acc
      | some (b₀, t₀) =>
        let c₀ := b₀ % 256
        -- 0xxxxxxx
        if c₀ < 0x80 then loop n t₀ (acc ++ cpStr c₀)
        -- 110xxxxx 10xxxxxx
        else if c₀ / 0x20 == 0x06 then
          match uncons t₀ with
          | none          => invalid
          | some (b₁, t₁) =>
            let c₁ := b₁ % 256
            let r := (c₀ % 0x20) * 0x40 + c₁ % 0x40
            if cont c₁ && 0x80 ≤ r
            then loop n t₁ (acc ++ cpStr r)
            else invalid
        -- 1110xxxx 10xxxxxx 10xxxxxx
        else if c₀ / 0x10 == 0x0e then
          match uncons t₀ with
          | none          => invalid
          | some (b₁, t₁) =>
            match uncons t₁ with
            | none          => invalid
            | some (b₂, t₂) =>
              let c₁ := b₁ % 256
              let c₂ := b₂ % 256
              let r := (c₀ % 0x10) * 0x1000 + (c₁ % 0x40) * 0x40 + c₂ % 0x40
              if cont c₁ && cont c₂ && 0x800 ≤ r && (r < 0xd800 || (0xdfff < r && r < 0x110000))
              then loop n t₂ (acc ++ cpStr r)
              else invalid
        -- 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
        else if c₀ / 0x08 == 0x1e then
          match uncons t₀ with
          | none          => invalid
          | some (b₁, t₁) =>
            match uncons t₁ with
            | none          => invalid
            | some (b₂, t₂) =>
              match uncons t₂ with
              | none          => invalid
              | some (b₃, t₃) =>
                let c₁ := b₁ % 256
                let c₂ := b₂ % 256
                let c₃ := b₃ % 256
                let r := (c₀ % 0x08) * 0x40000 + (c₁ % 0x40) * 0x1000 + (c₂ % 0x40) * 0x40 + c₃ % 0x40
                if cont c₁ && cont c₂ && cont c₃ && 0x10000 ≤ r && r < 0x110000
                then loop n t₃ (acc ++ cpStr r)
                else invalid
        else invalid

/-- `decodeUtf8.loop` over the characters, for compiled code. `decodeUtf8.loop` reads with
    `uncons`, which copies the rest of the string. -/
def decodeUtf8Go : Nat → List Char → String → Except String String
  | 0    , _       , acc => pure acc
  | _ + 1, []      , acc => pure acc
  | n + 1, b₀ :: t₀, acc =>
    let c₀ := b₀.toNat % 256
    if c₀ < 0x80 then decodeUtf8Go n t₀ (acc ++ cpStr c₀)
    else if c₀ / 0x20 == 0x06 then
      match t₀ with
      | []       => decodeUtf8.invalid
      | b₁ :: t₁ =>
        let c₁ := b₁.toNat % 256
        let r := (c₀ % 0x20) * 0x40 + c₁ % 0x40
        if decodeUtf8.cont c₁ && 0x80 ≤ r
        then decodeUtf8Go n t₁ (acc ++ cpStr r)
        else decodeUtf8.invalid
    else if c₀ / 0x10 == 0x0e then
      match t₀ with
      | []       => decodeUtf8.invalid
      | b₁ :: t₁ =>
        match t₁ with
        | []       => decodeUtf8.invalid
        | b₂ :: t₂ =>
          let c₁ := b₁.toNat % 256
          let c₂ := b₂.toNat % 256
          let r := (c₀ % 0x10) * 0x1000 + (c₁ % 0x40) * 0x40 + c₂ % 0x40
          if decodeUtf8.cont c₁ && decodeUtf8.cont c₂ && 0x800 ≤ r && (r < 0xd800 || (0xdfff < r && r < 0x110000))
          then decodeUtf8Go n t₂ (acc ++ cpStr r)
          else decodeUtf8.invalid
    else if c₀ / 0x08 == 0x1e then
      match t₀ with
      | []       => decodeUtf8.invalid
      | b₁ :: t₁ =>
        match t₁ with
        | []       => decodeUtf8.invalid
        | b₂ :: t₂ =>
          match t₂ with
          | []       => decodeUtf8.invalid
          | b₃ :: t₃ =>
            let c₁ := b₁.toNat % 256
            let c₂ := b₂.toNat % 256
            let c₃ := b₃.toNat % 256
            let r := (c₀ % 0x08) * 0x40000 + (c₁ % 0x40) * 0x1000 + (c₂ % 0x40) * 0x40 + c₃ % 0x40
            if decodeUtf8.cont c₁ && decodeUtf8.cont c₂ && decodeUtf8.cont c₃ && 0x10000 ≤ r && r < 0x110000
            then decodeUtf8Go n t₃ (acc ++ cpStr r)
            else decodeUtf8.invalid
    else decodeUtf8.invalid

theorem decodeUtf8Go_eq (n : Nat) (l : List Char) (acc : String) :
    decodeUtf8Go n l acc = decodeUtf8.loop n ⟨l⟩ acc := by
  induction n generalizing l acc with
  | zero => rw [decodeUtf8Go, decodeUtf8.loop]
  | succ n ih =>
    rcases l with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, t⟩⟩⟩⟩ <;>
      simp only [decodeUtf8Go, decodeUtf8.loop, uncons_cons, uncons_nil, ih]

def decodeUtf8Impl (bs : ByteString) : Except String String := decodeUtf8Go bs.length bs.data.data ""

/-- Compiled code runs `decodeUtf8Impl` for `decodeUtf8`. -/
@[csimp] theorem decodeUtf8_eq_impl : @decodeUtf8 = @decodeUtf8Impl := by
  funext bs; rw [decodeUtf8, decodeUtf8Impl, decodeUtf8Go_eq]

end PlutusCore.StringInternal

export PlutusCore.StringInternal
  ( -- builtin functions
    appendString
    decodeUtf8
    emptyString
    encodeUtf8
    equalsString
    utf8EncodeCode
    utf8EncodeChar
    utf8DecodeChar?
  )

end PlutusCore.String

