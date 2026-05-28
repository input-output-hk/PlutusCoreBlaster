import PlutusCore.Cbor.Basic

namespace PlutusCore.Cbor
open PlutusCore.Cbor.Internal

-- ==============
-- =  Encoding  =
-- ==============

example : e₈ 7234295460216005990 = "deadbeef".toList := rfl

example : splitToChunks "" = [] := by native_decide

example : splitToChunks "1234567890123456789012345678901234567890123456789012345678901234" =
  [ "1234567890123456789012345678901234567890123456789012345678901234" ] := by native_decide

example : splitToChunks  "12345678901234567890123456789012345678901234567890123456789012345" =
  [ "1234567890123456789012345678901234567890123456789012345678901234"
  , "5"
  ] := by native_decide

example : splitToChunks "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
  [ "1234567890123456789012345678901234567890123456789012345678901234"
  , "1234567890123456789012345678901234567890123456789012345678901234"
  , "56"
  ] := by native_decide

example : encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234" =
  .some ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234") := by native_decide

example : encodeBytestring "12345678901234567890123456789012345678901234567890123456789012345" =
  .some ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x41"     ++ "5"
         ++ "\xFF") := by native_decide

example : encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
  .some ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x42"     ++ "56"
         ++ "\xFF") := by native_decide

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
example : (encodeData (.Constr (2 ^ 64) [.I 1])).bind decodeData = .none := by native_decide
example : (encodeData (.Constr (-1) [])).bind decodeData = .none := by native_decide

-- Map round-trips through decodePairList (definite-length map header + key/value pairs).
example : (encodeData (.Map [(.I 1, .B { data := "aa" }), (.List [], .Constr 3 [.I 4])])).bind decodeData
  = .some ("", .Map [(.I 1, .B { data := "aa" }), (.List [], .Constr 3 [.I 4])]) := by native_decide

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

end PlutusCore.Cbor
