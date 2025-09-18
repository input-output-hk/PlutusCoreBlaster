import PlutusCore.ByteString.Basic

namespace PlutusCore.String
open PlutusCore.ByteString

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

/-- Coverts String to ByteString using utf8 encoding -/
def encodeUtf8 (s : String) : ByteString := ⟨⟨s.data.flatMap utf8EncodeChar⟩⟩

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
-/
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

end PlutusCore.StringInternal

export PlutusCore.StringInternal
  ( -- builtin functions
    appendString
    decodeUtf8
    emptyString
    encodeUtf8
    equalsString
    utf8EncodeChar
    utf8DecodeChar?
  )

end PlutusCore.String

