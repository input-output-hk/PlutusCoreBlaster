import Blaster
import PlutusCore.Cbor.Basic

namespace PlutusCore.Cbor
open PlutusCore.Cbor.CborInternal
open PlutusCore.Integer (Integer)

-- ==============
-- =  Encoding  =
-- ==============

example : e₈ 7234295460216005990 = "deadbeef".toList := rfl

def example_1 : Prop := splitToChunks "" = []
example : example_1 := by simp [example_1]; native_decide

def example_2 : Prop :=
  splitToChunks "1234567890123456789012345678901234567890123456789012345678901234" =
  [ "1234567890123456789012345678901234567890123456789012345678901234" ]

example : example_2 := by simp [example_2]; native_decide

def example_3 : Prop := splitToChunks  "12345678901234567890123456789012345678901234567890123456789012345" =
  [ "1234567890123456789012345678901234567890123456789012345678901234"
  , "5"
  ]

example : example_3 := by simp [example_3]; native_decide

def example_4 : Prop :=
  splitToChunks "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
  [ "1234567890123456789012345678901234567890123456789012345678901234"
  , "1234567890123456789012345678901234567890123456789012345678901234"
  , "56"
  ]
example : example_4 := by simp [example_4]; native_decide

def example_5 : Prop :=
  encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234" =
  "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
example : example_5 := by simp [example_5]; native_decide

def example_6 : Prop :=
  encodeBytestring "12345678901234567890123456789012345678901234567890123456789012345" =
  "\x5F"
  ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
  ++ "\x41"     ++ "5"
  ++ "\xFF"

example : example_6 := by simp [example_6]; native_decide

example : encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
  "\x5F"
  ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
  ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
  ++ "\x42"     ++ "56"
  ++ "\xFF" := by native_decide

example : encodeData (.I 12) = .some "\x0c"     := by simp [encodeData, encodeInt, encodeHead]
example : encodeData (.I 42) = .some "\x18\x2a" := by simp [encodeData, encodeInt, encodeHead]

example :
    encodeData (
      .Constr 0 [
        .Constr 0 [.I 1284531],
        .I 1739713998000
      ]
    ) = .some "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff" := by native_decide

example :
  encodeData (
    .Constr 0 [
      .I 144375414,
      .I 22710,
      .I 4387720097
    ]
  ) = .some "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff" := by native_decide

-- ==============
-- =  Decoding  =
-- ==============

example : d₈ "deadbeef".toList = .some ([], 7234295460216005990) := by rfl
example : d₁ "deadbeef".toList = .some ("eadbeef".toList, 100)   := by rfl

example : decodeBytestring ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234") =
  .some ("", "1234567890123456789012345678901234567890123456789012345678901234") := by native_decide

example : decodeData "\x0C"     = .some ("", .I 12) := by native_decide
example : decodeData "\x18\x2A" = .some ("", .I 42) := by native_decide

example : decodeData "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff\x34\x32"
    = .some (
        "42",
        .Constr 0 [
          .Constr 0 [.I 1284531],
          .I 1739713998000
        ]
      ) := by native_decide

example : decodeData "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff\x43\x62\x6f\x72\x44\x61\x74\x61"
  = .some (
      "CborData",
      .Constr 0 [
        .I 144375414,
        .I 22710,
        .I 4387720097
      ]
  ) := by native_decide

-- Empty collections encode as a DEFINITE empty array (0x80), matching the on-chain
-- serialiseData builtin (aiken/cbor.serialise), not an indefinite 0x9f..0xff.
-- (The List [], Constr 0, and nested cases are byte-anchored in the reference fixtures below.)
example : encodeData (.Constr 1 []) = .some "\xd8\x7a\x80" := by native_decide
example : encodeData (.Constr 7 []) = .some "\xd9\x05\x00\x80" := by native_decide

-- decodeData round-trips negative bignums (tag 3), not just positive (tag 2).
example : (encodeData (.I (-(2 ^ 512 + 1)))).bind decodeData = .some ("", .I (-(2 ^ 512 + 1))) := by native_decide

-- Byte-anchored DECODE vector pinning the tag-1/tag-3 boundary: `-(2^64)` is the largest negative
-- on the major-type-1 side. `-(2^64+1)` (first tag-3 negative bignum) is byte-anchored in the
-- reference fixtures below, and would decode wrong under the old `1 - m` sign bug.
example : decodeData "\x3b\xff\xff\xff\xff\xff\xff\xff\xff" = .some ("", .I (-(2 ^ 64))) := by native_decide
example : (encodeData (.I (2 ^ 512))).bind decodeData = .some ("", .I (2 ^ 512)) := by native_decide
example : (encodeData (.Constr 1 [])).bind decodeData = .some ("", .Constr 1 []) := by native_decide

-- An empty ByteString is a definite 0-length string (0x40), not zero bytes, and round-trips.
-- (The bare 0x40 and the empty-B-in-map cases are byte-anchored in the reference fixtures below.)
example : (encodeData (.B { data := "" })).bind decodeData = .some ("", .B { data := "" }) := by native_decide
example : (encodeData (.List [.B { data := "" }, .I 5])).bind decodeData
  = .some ("", .List [.B { data := "" }, .I 5]) := by native_decide

-- Constructor index > 127 uses the tag-102 fallback. The index must be a direct Word64: in-range
-- indices (128, 2^63-1, 2^64-1) are byte-anchored in the reference fixtures below. An index >= 2^64
-- or a negative index is rejected on decode, matching the real ledger decoder (decodeWord64), even
-- though serialiseData will emit it (write-only).

example : encodeData (.Constr (2 ^ 64) [.I 1]) = some "\xD8\x66\x82\xC2\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00\x9F\x01\xFF" := by native_decide
example : (encodeData (.Constr (2 ^ 64) [.I 1])).bind decodeData = .none := by native_decide
example : (encodeData (.Constr (-1) [])).bind decodeData = .none := by native_decide

-- Map round-trips through decodePairList (definite-length map header + key/value pairs).
example : (encodeData (.Map [(.I 1, .B { data := "aa" }), (.List [], .Constr 3 [.I 4])])).bind decodeData
  = .some ("", .Map [(.I 1, .B { data := "aa" }), (.List [], .Constr 3 [.I 4])]) := by native_decide

-- Haskell conformance for indefinite-length forms. Data.hs accepts BOTH the canonical definite
-- encoding and an indefinite one, for maps (decodeMapLenOrIndef) and the tag-102 constructor wrapper
-- (decodeConstrExtended via decodeListLenOrIndef). For each shape below, the canonical definite form
-- is exactly what encodeData emits, and both the definite form and the indefinite form decode to the
-- SAME value. That pins the indefinite-form leniency to semantic equivalence with the canonical
-- encoding, not merely to acceptance.

-- Map [(I 1, I 2)]
example : encodeData (.Map [(.I 1, .I 2)]) = .some "\xa1\x01\x02"          := by native_decide
example : decodeData "\xa1\x01\x02"        = .some ("", .Map [(.I 1, .I 2)]) := by native_decide
example : decodeData "\xbf\x01\x02\xff"    = .some ("", .Map [(.I 1, .I 2)]) := by native_decide
-- Map []
example : encodeData (.Map []) = .some "\xa0"        := by native_decide
example : decodeData "\xa0"    = .some ("", .Map []) := by native_decide
example : decodeData "\xbf\xff" = .some ("", .Map []) := by native_decide
-- Constr 200 [] (index > 127 uses the tag-102 wrapper)
example : encodeData (.Constr 200 [])   = .some "\xd8\x66\x82\x18\xc8\x80"     := by native_decide
example : decodeData "\xd8\x66\x82\x18\xc8\x80"     = .some ("", .Constr 200 []) := by native_decide
example : decodeData "\xd8\x66\x9f\x18\xc8\x80\xff" = .some ("", .Constr 200 []) := by native_decide
-- Constr 200 [I 1, I 2]
example : encodeData (.Constr 200 [.I 1, .I 2]) = .some "\xd8\x66\x82\x18\xc8\x9f\x01\x02\xff"      := by native_decide
example : decodeData "\xd8\x66\x82\x18\xc8\x9f\x01\x02\xff"      = .some ("", .Constr 200 [.I 1, .I 2]) := by native_decide
example : decodeData "\xd8\x66\x9f\x18\xc8\x9f\x01\x02\xff\xff"  = .some ("", .Constr 200 [.I 1, .I 2]) := by native_decide

-- Inside the indefinite wrapper the args may be definite (0x82) or indefinite (0x9f), both accepted
-- by Data.hs and both decoding identically.
example : decodeData "\xd8\x66\x9f\x18\xc8\x82\x01\x02\xff" = .some ("", .Constr 200 [.I 1, .I 2]) := by native_decide
-- The indefinite wrapper enforces the same structure Data.hs does: a Word64 index, exactly two
-- elements (index and args), and a closing break. A negative index, a missing break, or a third
-- element is rejected. Nesting an indefinite wrapper inside another decodes.
example : decodeData "\xd8\x66\x9f\x20\x80\xff"         = .none := by native_decide
example : decodeData "\xd8\x66\x9f\x18\xc8\x80"         = .none := by native_decide
example : decodeData "\xd8\x66\x9f\x18\xc8\x80\x80\xff" = .none := by native_decide
example : decodeData "\xd8\x66\x9f\x18\xc8\x9f\xd8\x66\x9f\x18\xc9\x80\xff\xff\xff" = .some ("", .Constr 200 [.Constr 201 []]) := by native_decide

-- Additional Data.hs-conformance coverage. The index through the indefinite wrapper is read by a
-- separate path (decodeIndefConstr), so anchor it at the same Word64 boundaries the definite path
-- uses, and reject an out-of-range (bignum) index there too.
example : decodeData "\xd8\x66\x9f\x1b\xff\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff\xff" = .some ("", .Constr (2 ^ 64 - 1) [.I 1]) := by native_decide
example : decodeData "\xd8\x66\x9f\x1b\x80\x00\x00\x00\x00\x00\x00\x00\x80\xff" = .some ("", .Constr (2 ^ 63) []) := by native_decide
example : decodeData "\xd8\x66\x9f\xc2\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00\x80\xff" = .none := by native_decide
-- A non-canonical small index (< 128) is valid in the wrapper too (Data.hs decodeWord64 accepts it).
example : decodeData "\xd8\x66\x9f\x00\x80\xff" = .some ("", .Constr 0 []) := by native_decide
-- The "exactly two elements" rule is on the OUTER wrapper array; the args list itself is any length.
example : decodeData "\xd8\x66\x9f\x18\xc8\x83\x01\x02\x03\xff" = .some ("", .Constr 200 [.I 1, .I 2, .I 3]) := by native_decide
-- Reject a third element or a missing break when the args is an INDEFINITE list (the other args branch).
example : decodeData "\xd8\x66\x9f\x18\xc8\x9f\xff\x00\xff" = .none := by native_decide
example : decodeData "\xd8\x66\x9f\x18\xc8\x9f\xff" = .none := by native_decide
-- Indefinite maps: multiple pairs preserve order, a break between key and value is rejected, maps nest.
example : decodeData "\xbf\x01\x02\x03\x04\xff" = .some ("", .Map [(.I 1, .I 2), (.I 3, .I 4)]) := by native_decide
example : decodeData "\xbf\x01\xff" = .none := by native_decide
example : decodeData "\xbf\x01\xbf\x02\x03\xff\xff" = .some ("", .Map [(.I 1, .Map [(.I 2, .I 3)])]) := by native_decide
-- Cross-form nesting: an indefinite map inside an indefinite-wrapper constructor's args.
example : decodeData "\xd8\x66\x9f\x18\xc8\x9f\xbf\x01\x02\xff\xff\xff" = .some ("", .Constr 200 [.Map [(.I 1, .I 2)]]) := by native_decide

-- Reference fixtures: golden CBOR vectors for the shapes this PR touches (empty containers, empty
-- bytestring, negative bignums, tag-102 indices, nesting). Each pins `encodeData` to fixed bytes
-- and `decodeData` to invert them. The bytes are the canonical CBOR encoding mandated by the
-- reference (`Data.hs` / cborg / RFC 8949), hand-verifiable byte by byte, so the encode direction
-- is a genuine anchor and not a self-referential round-trip.
-- emptyList
example : encodeData (.List []) = .some "\x80" := by native_decide
example : decodeData "\x80" = .some ("", .List []) := by native_decide
-- emptyConstr0
example : encodeData (.Constr 0 []) = .some "\xd8\x79\x80" := by native_decide
example : decodeData "\xd8\x79\x80" = .some ("", .Constr 0 []) := by native_decide
-- emptyConstr5
example : encodeData (.Constr 5 []) = .some "\xd8\x7e\x80" := by native_decide
example : decodeData "\xd8\x7e\x80" = .some ("", .Constr 5 []) := by native_decide
-- emptyB
example : encodeData (.B { data := "" }) = .some "\x40" := by native_decide
example : decodeData "\x40" = .some ("", .B { data := "" }) := by native_decide
-- mapEmptyB
example : encodeData (.Map [(.B { data := "" }, .I 0)]) = .some "\xa1\x40\x00" := by native_decide
example : decodeData "\xa1\x40\x00" = .some ("", .Map [(.B { data := "" }, .I 0)]) := by native_decide
-- negBignum64
example : encodeData (.I (-(2 ^ 64 + 1))) = .some "\xc3\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00" := by native_decide
example : decodeData "\xc3\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00" = .some ("", .I (-(2 ^ 64 + 1))) := by native_decide
-- negBignum128
example : encodeData (.I (-(2 ^ 128))) = .some "\xc3\x50\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff" := by native_decide
example : decodeData "\xc3\x50\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff" = .some ("", .I (-(2 ^ 128))) := by native_decide
-- constr128
example : encodeData (.Constr 128 []) = .some "\xd8\x66\x82\x18\x80\x80" := by native_decide
example : decodeData "\xd8\x66\x82\x18\x80\x80" = .some ("", .Constr 128 []) := by native_decide
-- constrBig (2^63-1)
example : encodeData (.Constr (2 ^ 63 - 1) [.I 1]) = .some "\xd8\x66\x82\x1b\x7f\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff" := by native_decide
example : decodeData "\xd8\x66\x82\x1b\x7f\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff" = .some ("", .Constr (2 ^ 63 - 1) [.I 1]) := by native_decide
-- constrMax (2^64-1, the largest in-range Word64 index)
example : encodeData (.Constr (2 ^ 64 - 1) [.I 1]) = .some "\xd8\x66\x82\x1b\xff\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff" := by native_decide
example : decodeData "\xd8\x66\x82\x1b\xff\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff" = .some ("", .Constr (2 ^ 64 - 1) [.I 1]) := by native_decide
-- nested
example : encodeData (.Constr 0 [.List [], .I 5]) = .some "\xd8\x79\x9f\x80\x05\xff" := by native_decide
example : decodeData "\xd8\x79\x9f\x80\x05\xff" = .some ("", .Constr 0 [.List [], .I 5]) := by native_decide
-- mapKV
example : encodeData (.Map [(.I 0, .I 1)]) = .some "\xa1\x00\x01" := by native_decide
example : decodeData "\xa1\x00\x01" = .some ("", .Map [(.I 0, .I 1)]) := by native_decide
-- listII
example : encodeData (.List [.I 1, .I 2]) = .some "\x9f\x01\x02\xff" := by native_decide
example : decodeData "\x9f\x01\x02\xff" = .some ("", .List [.I 1, .I 2]) := by native_decide


-- Blaster Test Cases on encodeData

set_option warn.sorry false

#blaster (only-optimize: 1) [example_1]
#blaster (only-optimize: 1) [example_2]
#blaster (only-optimize: 1) [example_3]
#blaster (only-optimize: 1) [example_4]
#blaster (only-optimize: 1) [example_5]
#blaster (only-optimize: 1) [example_6]

example : encodeData (.List [.I 1]) ≠ none := by blaster (only-optimize: 1)

-- example : encodeBytestring "12345678901234567890123456789012345678901234567890123456789012345" =
--   "\x5F"
--   ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
--   ++ "\x41"     ++ "5"
--   ++ "\xFF" := by blaster (solve-result: 2) (only-optimize: 1)

-- example : encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
--   "\x5F"
--   ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
--   ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
--   ++ "\x42"     ++ "56"
--   ++ "\xFF" := by blaster

example : encodeData (.I 12) = .some "\x0c"     := by blaster (only-optimize: 1)
example : encodeData (.I 42) = .some "\x18\x2a" := by blaster (only-optimize: 1)

example :
    encodeData (
      .Constr 0 [
        .Constr 0 [.I 1284531],
        .I 1739713998000
      ]
    ) = .some "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff" := by blaster (only-optimize: 1)

example :
  encodeData (
    .Constr 0 [
      .I 144375414,
      .I 22710,
      .I 4387720097
    ]
  ) = .some "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff" := by native_decide

-- theorem ser_one : ∀ (i : Integer), 0 ≤ i ∧ i ≤ 18446744073709551615 → (encodeInt i).length = 1 := by blaster

-- theorem ser_one_bis : ∀ (i : Integer), 18446744073709551616 ≤ i → (encodeInt i).length = 1 := by sorry
-- theorem itos_blabla : ∀ (i : Nat), (itos i).length = 1 := by blaster

end PlutusCore.Cbor
