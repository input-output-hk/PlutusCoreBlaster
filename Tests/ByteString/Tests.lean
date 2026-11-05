import Tests.ByteString.Reference

/-! # The byte-level builtins, rewritten over `PlutusCore.Bytes`, against their originals

Each builtin is run on many inputs next to its `Char`-based original in
`Tests.ByteString.Reference`, and must return the same result: the same bytes, the same number,
the same error message. Readers are also run on strings with characters above 255 (not valid byte
strings), where they must agree too.

The last section checks that concrete evaluation still works through the seal on
`PlutusCore.Bytes.uncons`, in `#guard` and in proofs. -/

namespace Tests.ByteString.Tests

open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)

namespace Ref
export Tests.ByteString.Reference
  (consByteStringV1 consByteStringV2 sliceByteString indexByteString integerToByteString
   byteStringToInteger encodeUtf8 decodeUtf8 encodeData)
end Ref

/-! ## Inputs -/

/-- Same result, comparing errors by message. -/
def sameE [BEq α] : Except String α → Except String α → Bool
  | .ok a   , .ok b    => a == b
  | .error e, .error f => e == f
  | _       , _        => false

/-- `n` pseudo-random numbers below `bound`, from `seed` (a linear congruential generator). -/
def randoms (seed n bound : Nat) : List Nat :=
  (go n (seed * 7919 + 1) []).reverse
where
  go : Nat → Nat → List Nat → List Nat
    | 0    , _, acc => acc
    | k + 1, x, acc =>
      let x' := (x * 1103515245 + 12345) % 2147483648
      go k x' ((x' / 65536) % bound :: acc)

/-- The string whose characters have the given codes. -/
def ofCodes (l : List Nat) : String := String.mk (l.map Char.ofNat)

/-- The empty string, all one-byte strings, pseudo-random byte strings of up to 200 bytes, and
    strings of `n` equal bytes around the CBOR chunk size. -/
def byteStrings : List String :=
  [""] ++
  (List.range 256).map (fun b => ofCodes [b]) ++
  (List.range 60).map (fun i => ofCodes (randoms i (i * 3 % 50 + 2) 256)) ++
  [63, 64, 65, 127, 128, 129, 200].map (fun n => ofCodes (randoms n n 256))

/-- Strings with characters that are not bytes. -/
def wideStrings : List String :=
  ["Ā", "aŁb", "€uro", "😀x", ofCodes [0x10FFFF], ofCodes [0xFFFF, 0x10000], ofCodes [0x7FF, 0x800, 0xD7FF, 0xE000]]

def offsets : List Integer :=
  ((List.range 16).map (fun (i : Nat) => (i : Integer) - 3)) ++ [63, 64, 65, 100, 250, 2 ^ 70]

/-! ## `sliceByteString`, `indexByteString`, `consByteString` -/

#guard (byteStrings ++ wideStrings).all fun s =>
  offsets.all fun a => offsets.all fun k =>
    PlutusCore.ByteString.sliceByteString a k ⟨s⟩ == Ref.sliceByteString a k ⟨s⟩

#guard (byteStrings ++ wideStrings).all fun s =>
  ((List.range (s.length + 7)).map (fun (j : Nat) => (j : Integer) - 3) ++ [2 ^ 70]).all fun j =>
    sameE (PlutusCore.ByteString.indexByteString ⟨s⟩ j) (Ref.indexByteString ⟨s⟩ j)

#guard ["", "\x00", "ab\xff", "Ł"].all fun s =>
  ((List.range 1400).map (fun (n : Nat) => (n : Integer) - 700) ++ [2 ^ 70, -(2 ^ 70)]).all fun n =>
    PlutusCore.ByteString.consByteStringV1 n ⟨s⟩ == Ref.consByteStringV1 n ⟨s⟩ &&
    sameE (PlutusCore.ByteString.consByteStringV2 n ⟨s⟩) (Ref.consByteStringV2 n ⟨s⟩)

/-! ## `byteStringToInteger` and `integerToByteString` -/

/-- Every byte string of length 2. -/
def pairs : List String :=
  (List.range 65536).map fun i => ofCodes [i / 256, i % 256]

#guard (pairs ++ byteStrings ++ wideStrings).all fun s =>
  [true, false].all fun e =>
    PlutusCore.Bitwise.byteStringToInteger e s == Ref.byteStringToInteger e s

def widths : List Integer := [-1, 0, 1, 2, 3, 4, 5, 8, 9, 31, 32, 33, 8192, 8193]

def numbers : List Integer :=
  [-(2 ^ 64), -1, 0, 1, 2, 255, 256, 257, 65535, 65536, 0x123456, 2 ^ 24 - 1, 2 ^ 24,
   2 ^ 64 - 1, 2 ^ 64, 2 ^ 248, 2 ^ 256 - 1, 2 ^ 256, 2 ^ 65535, 2 ^ 65536 - 1, 2 ^ 65536] ++
  (List.range 30).map (fun i => (Ref.byteStringToInteger true (ofCodes (randoms (i + 100) (i + 1) 256)) : Integer))

#guard widths.all fun w => numbers.all fun n => [true, false].all fun e =>
  sameE (PlutusCore.Bitwise.integerToByteString e w n) (Ref.integerToByteString e w n)

/-! ## `encodeUtf8` and `decodeUtf8` -/

/-- Code points: all of the first 0x3000, every one around the 1–4 byte and surrogate boundaries,
    and a stride through the rest. `Char.ofNat` maps the surrogates to `'\x00'`. -/
def codes : List Nat :=
  List.range 0x3000 ++
  (List.range 0x500).map (· + 0xD600) ++
  (List.range 0x300).map (· + 0xFE00) ++
  (List.range 0x400).map (· + 0x10000) ++
  (List.range 0x400).map (· + 0x10FC00) ++
  (List.range 0x2000).map (· * 0x83 + 0x3000)

def textStrings : List String :=
  ["", "héllo €", "😀", ofCodes [0x61, 0x10FFFF, 0x62]] ++ wideStrings ++ byteStrings.take 300 ++
  (List.range 40).map (fun i => ofCodes ((randoms (i + 7) (i % 9 + 1) codes.length).map (codes.getD · 0)))

#guard codes.all fun c =>
  let s := String.singleton (Char.ofNat c)
  PlutusCore.String.encodeUtf8 s == Ref.encodeUtf8 s

#guard textStrings.all fun s => PlutusCore.String.encodeUtf8 s == Ref.encodeUtf8 s

/-- The byte strings `decodeUtf8` is checked on: every string of up to two bytes, three- and
    four-byte strings over lead bytes 0xC0–0xFF and boundary continuation bytes, the encodings of
    all of `codes` and `textStrings`, and strings with characters that are not bytes. -/
def utf8Inputs : List String :=
  let edge := [0x00, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xFF]
  let leads := (List.range 64).map (· + 0xC0)
  pairs ++ byteStrings ++
  (leads.flatMap fun a => edge.flatMap fun b => edge.map fun c => ofCodes [a, b, c]) ++
  ((List.range 32).map (· + 0xE0) |>.flatMap fun a => edge.flatMap fun b => edge.flatMap fun c =>
    edge.map fun d => ofCodes [a, b, c, d]) ++
  (codes.map fun c => (Ref.encodeUtf8 (String.singleton (Char.ofNat c))).data) ++
  (textStrings.map fun s => (Ref.encodeUtf8 s).data) ++
  wideStrings ++ ["Ł", ofCodes [0x1C3, 0x1A9], ofCodes [0x1F0, 0x19F, 0x198, 0x180]]

#guard utf8Inputs.all fun s =>
  sameE (PlutusCore.String.decodeUtf8 ⟨s⟩) (Ref.decodeUtf8 ⟨s⟩)

/-! ## `serialiseData` (`encodeData`) -/

def ints : List Integer :=
  [0, 1, 23, 24, 255, 256, 65535, 65536, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
   2 ^ 512, 2 ^ 520 - 1, 2 ^ 4096,
   -1, -24, -25, -256, -257, -(2 ^ 64), -(2 ^ 64) - 1, -(2 ^ 512), -(2 ^ 4096)]

def datas : List Data :=
  let leaves : List Data := ints.map .I ++ byteStrings.map (fun s => .B ⟨s⟩) ++ wideStrings.map (fun s => .B ⟨s⟩)
  let ctags : List Integer := [0, 1, 6, 7, 100, 127, 128, 1000, 2 ^ 64 - 1, 2 ^ 64, -1]
  leaves ++
  ctags.map (fun i => .Constr i []) ++
  ctags.map (fun i => .Constr i (leaves.take 3)) ++
  [ .List [], .Map [], .List (leaves.take 40), .Map ((leaves.take 20).zip (leaves.drop 20 |>.take 20)),
    .Constr 0 [.List [.I 1, .B ⟨"ab"⟩], .Map [(.I 1, .Constr 3 [.I 4])], .B (⟨ofCodes (randoms 5 300 256)⟩)],
    .List ((List.range 30).map (fun i => .List ((List.range i).map (fun (j : Nat) => .I (j : Integer))))) ]

#guard datas.all fun d => PlutusCore.Cbor.encodeData d == Ref.encodeData d

/-! ## Known answers -/

#guard PlutusCore.Bitwise.byteStringToInteger true  "\x01\x02" == 258
#guard PlutusCore.Bitwise.byteStringToInteger false "\x01\x02" == 513
#guard (PlutusCore.Bitwise.integerToByteString true 4 258).toOption == some "\x00\x00\x01\x02"
#guard PlutusCore.ByteString.sliceByteString 1 2 ⟨"abcd"⟩ == ⟨"bc"⟩
#guard (PlutusCore.ByteString.indexByteString ⟨"abcd"⟩ 3).toOption == some 0x64
#guard (PlutusCore.ByteString.consByteStringV2 0x61 ⟨"bc"⟩).toOption == some ⟨"abc"⟩
#guard PlutusCore.String.encodeUtf8 "€" == ⟨"\xe2\x82\xac"⟩
#guard (PlutusCore.String.decodeUtf8 (PlutusCore.String.encodeUtf8 "héllo €😀")).toOption == some "héllo €😀"
#guard (PlutusCore.String.decodeUtf8 ⟨"\xed\xa0\x80"⟩).toOption == none   -- an encoded surrogate
#guard PlutusCore.Cbor.encodeData (.B ⟨"\x01\x02"⟩) == some "\x42\x01\x02"

-- A byte string of the maximal width `integerToByteString` produces round-trips.
#guard
  let n : Integer := 2 ^ 65536 - 1
  match PlutusCore.Bitwise.integerToByteString true 8192 n with
  | .ok s => s.length == 8192 && PlutusCore.Bitwise.byteStringToInteger true s == n
  | .error _ => false

/-! ## Proofs about concrete values go through the seal

`rfl` and `decide` stop at the sealed `PlutusCore.Bytes.uncons`; unfolding everything does not. -/

example : PlutusCore.Bitwise.byteStringToInteger true "\x01\x02" = 258 := by with_unfolding_all rfl
example : PlutusCore.ByteString.sliceByteString 1 2 ⟨"abcd"⟩ = ⟨"bc"⟩ := by with_unfolding_all rfl
example : PlutusCore.String.decodeUtf8 ⟨"\xe2\x82\xac"⟩ = .ok "€" := by with_unfolding_all rfl
example : PlutusCore.Cbor.encodeData (.B ⟨"\x01\x02"⟩) = some "\x42\x01\x02" := by with_unfolding_all rfl
example : PlutusCore.Bitwise.byteStringToInteger true "\x01\x02" = 258 := by decide +kernel

end Tests.ByteString.Tests
