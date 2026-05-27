import PlutusCore.Cbor.Basic

namespace PlutusCore.Cbor
open PlutusCore.Cbor.CborInternal

/-- Convert a String of codepoint-as-byte characters to its `ByteArray` representation.
    Test-only helper: matches the historical convention where each Char in 0–255 stands
    for the byte with the same value (the same convention used by the UPLC `ByteString`
    domain wrapper). -/
private def s2ba (s : String) : ByteArray := ⟨(Char.toUInt8 <$> s.data).toArray⟩

-- ==============
-- =  Encoding  =
-- ==============

example : e₈ 7234295460216005990 = "deadbeef".toUTF8 := by rfl

example : splitToChunks .empty = [] := by rfl

example : splitToChunks (s2ba "1234567890123456789012345678901234567890123456789012345678901234") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234" ] := by native_decide

example : splitToChunks (s2ba "12345678901234567890123456789012345678901234567890123456789012345") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "5"
  ] := by native_decide

example : splitToChunks (s2ba "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "56"
  ] := by native_decide

example : encodeBytestring (s2ba "1234567890123456789012345678901234567890123456789012345678901234") =
  .some (s2ba ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234")) := by native_decide

example : encodeBytestring (s2ba "12345678901234567890123456789012345678901234567890123456789012345") =
  .some (s2ba ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x41"     ++ "5"
         ++ "\xFF")) := by native_decide

example : encodeBytestring (s2ba "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456") =
  .some (s2ba ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x42"     ++ "56"
         ++ "\xFF")) := by native_decide

example : encodeData (.I 12) = .some (s2ba "\x0c")     := by native_decide
example : encodeData (.I 42) = .some (s2ba "\x18\x2a") := by native_decide

example :
    encodeData (
      .Constr 0 [
        .Constr 0 [.I 1284531],
        .I 1739713998000
      ]
    ) = .some (s2ba "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff") := by native_decide

example :
  encodeData (
    .Constr 0 [
      .I 144375414,
      .I 22710,
      .I 4387720097
    ]
  ) = .some (s2ba "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff") := by native_decide

-- ==============
-- =  Decoding  =
-- ==============

example :
    d₈ { input := s2ba "deadbeef", pos := 0 } =
    .some ({ input := s2ba "deadbeef", pos := 8 }, 7234295460216005990) := by native_decide

example :
    d₁ { input := s2ba "deadbeef", pos := 0 } =
    .some ({ input := s2ba "deadbeef", pos := 1 }, 100) := by native_decide

example : decodeBytestring (s2ba ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234")) =
  .some (s2ba "", s2ba "1234567890123456789012345678901234567890123456789012345678901234") := by native_decide

example : decodeData (s2ba "\x0C")     = .some (s2ba "", .I 12) := by native_decide
example : decodeData (s2ba "\x18\x2A") = .some (s2ba "", .I 42) := by native_decide

example : decodeData (s2ba "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff\x34\x32")
    = .some (
        s2ba "42",
        .Constr 0 [
          .Constr 0 [.I 1284531],
          .I 1739713998000
        ]
      ) := by native_decide

example : decodeData (s2ba "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff\x43\x62\x6f\x72\x44\x61\x74\x61")
  = .some (
      s2ba "CborData",
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
example : (encodeData (.I (-(2 ^ 512 + 1)))).bind (decodeData ∘ s2ba) = .some (s2ba "", .I (-(2 ^ 512 + 1))) := by native_decide

-- Byte-anchored DECODE vector pinning the tag-1/tag-3 boundary: `-(2^64)` is the largest negative
-- on the major-type-1 side. `-(2^64+1)` (first tag-3 negative bignum) is byte-anchored in the
-- reference fixtures below, and would decode wrong under the old `1 - m` sign bug.
example : decodeData (s2ba "\x3b\xff\xff\xff\xff\xff\xff\xff\xff") = .some (s2ba "", .I (-(2 ^ 64))) := by native_decide
example : (encodeData (.I (2 ^ 512))).bind (decodeData ∘ s2ba) = .some (s2ba "", .I (2 ^ 512)) := by native_decide
example : (encodeData (.Constr 1 [])).bind (decodeData ∘ s2ba) = .some (s2ba "", .Constr 1 []) := by native_decide

-- An empty ByteString is a definite 0-length string (0x40), not zero bytes, and round-trips.
-- (The bare 0x40 and the empty-B-in-map cases are byte-anchored in the reference fixtures below.)
example : (encodeData (.B { data := "" })).bind (decodeData ∘ s2ba) = .some (s2ba "", .B { data := "" }) := by native_decide
example : (encodeData (.List [.B { data := "" }, .I 5])).bind (decodeData ∘ s2ba)
  = .some (s2ba "", .List [.B { data := "" }, .I 5]) := by native_decide

-- Constructor index > 127 uses the tag-102 fallback. The index must be a direct Word64: in-range
-- indices (128, 2^63-1, 2^64-1) are byte-anchored in the reference fixtures below. An index >= 2^64
-- or a negative index is rejected on decode, matching the real ledger decoder (decodeWord64), even
-- though serialiseData will emit it (write-only).
example : (encodeData (.Constr (2 ^ 64) [.I 1])).bind (decodeData ∘ s2ba) = .none := by native_decide
example : (encodeData (.Constr (-1) [])).bind (decodeData ∘ s2ba) = .none := by native_decide

-- Map round-trips through decodePairList (definite-length map header + key/value pairs).
example : (encodeData (.Map [(.I 1, .B { data := "aa" }), (.List [], .Constr 3 [.I 4])])).bind (decodeData ∘ s2ba)
  = .some (s2ba "", .Map [(.I 1, .B { data := "aa" }), (.List [], .Constr 3 [.I 4])]) := by native_decide

-- Haskell conformance for indefinite-length forms. Data.hs accepts BOTH the canonical definite
-- encoding and an indefinite one, for maps (decodeMapLenOrIndef) and the tag-102 constructor wrapper
-- (decodeConstrExtended via decodeListLenOrIndef). For each shape below, the canonical definite form
-- is exactly what encodeData emits, and both the definite form and the indefinite form decode to the
-- SAME value. That pins the indefinite-form leniency to semantic equivalence with the canonical
-- encoding, not merely to acceptance.

-- Map [(I 1, I 2)]
example : encodeData (.Map [(.I 1, .I 2)]) = .some "\xa1\x01\x02"          := by native_decide
example : decodeData (s2ba "\xa1\x01\x02")        = .some (s2ba "", .Map [(.I 1, .I 2)]) := by native_decide
example : decodeData (s2ba "\xbf\x01\x02\xff")    = .some (s2ba "", .Map [(.I 1, .I 2)]) := by native_decide
-- Map []
example : encodeData (.Map []) = .some "\xa0"        := by native_decide
example : decodeData (s2ba "\xa0")    = .some (s2ba "", .Map []) := by native_decide
example : decodeData (s2ba "\xbf\xff") = .some (s2ba "", .Map []) := by native_decide
-- Constr 200 [] (index > 127 uses the tag-102 wrapper)
example : encodeData (.Constr 200 [])   = .some "\xd8\x66\x82\x18\xc8\x80"     := by native_decide
example : decodeData (s2ba "\xd8\x66\x82\x18\xc8\x80")     = .some (s2ba "", .Constr 200 []) := by native_decide
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x80\xff") = .some (s2ba "", .Constr 200 []) := by native_decide
-- Constr 200 [I 1, I 2]
example : encodeData (.Constr 200 [.I 1, .I 2]) = .some "\xd8\x66\x82\x18\xc8\x9f\x01\x02\xff"      := by native_decide
example : decodeData (s2ba "\xd8\x66\x82\x18\xc8\x9f\x01\x02\xff")      = .some (s2ba "", .Constr 200 [.I 1, .I 2]) := by native_decide
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x9f\x01\x02\xff\xff")  = .some (s2ba "", .Constr 200 [.I 1, .I 2]) := by native_decide

-- Inside the indefinite wrapper the args may be definite (0x82) or indefinite (0x9f), both accepted
-- by Data.hs and both decoding identically.
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x82\x01\x02\xff") = .some (s2ba "", .Constr 200 [.I 1, .I 2]) := by native_decide
-- The indefinite wrapper enforces the same structure Data.hs does: a Word64 index, exactly two
-- elements (index and args), and a closing break. A negative index, a missing break, or a third
-- element is rejected. Nesting an indefinite wrapper inside another decodes.
example : decodeData (s2ba "\xd8\x66\x9f\x20\x80\xff")         = .none := by native_decide
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x80")         = .none := by native_decide
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x80\x80\xff") = .none := by native_decide
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x9f\xd8\x66\x9f\x18\xc9\x80\xff\xff\xff") = .some (s2ba "", .Constr 200 [.Constr 201 []]) := by native_decide

-- Additional Data.hs-conformance coverage. The index through the indefinite wrapper is read by a
-- separate path (decodeIndefConstr), so anchor it at the same Word64 boundaries the definite path
-- uses, and reject an out-of-range (bignum) index there too.
example : decodeData (s2ba "\xd8\x66\x9f\x1b\xff\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff\xff") = .some (s2ba "", .Constr (2 ^ 64 - 1) [.I 1]) := by native_decide
example : decodeData (s2ba "\xd8\x66\x9f\x1b\x80\x00\x00\x00\x00\x00\x00\x00\x80\xff") = .some (s2ba "", .Constr (2 ^ 63) []) := by native_decide
example : decodeData (s2ba "\xd8\x66\x9f\xc2\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00\x80\xff") = .none := by native_decide
-- A non-canonical small index (< 128) is valid in the wrapper too (Data.hs decodeWord64 accepts it).
example : decodeData (s2ba "\xd8\x66\x9f\x00\x80\xff") = .some (s2ba "", .Constr 0 []) := by native_decide
-- The "exactly two elements" rule is on the OUTER wrapper array; the args list itself is any length.
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x83\x01\x02\x03\xff") = .some (s2ba "", .Constr 200 [.I 1, .I 2, .I 3]) := by native_decide
-- Reject a third element or a missing break when the args is an INDEFINITE list (the other args branch).
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x9f\xff\x00\xff") = .none := by native_decide
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x9f\xff") = .none := by native_decide
-- Indefinite maps: multiple pairs preserve order, a break between key and value is rejected, maps nest.
example : decodeData (s2ba "\xbf\x01\x02\x03\x04\xff") = .some (s2ba "", .Map [(.I 1, .I 2), (.I 3, .I 4)]) := by native_decide
example : decodeData (s2ba "\xbf\x01\xff") = .none := by native_decide
example : decodeData (s2ba "\xbf\x01\xbf\x02\x03\xff\xff") = .some (s2ba "", .Map [(.I 1, .Map [(.I 2, .I 3)])]) := by native_decide
-- Cross-form nesting: an indefinite map inside an indefinite-wrapper constructor's args.
example : decodeData (s2ba "\xd8\x66\x9f\x18\xc8\x9f\xbf\x01\x02\xff\xff\xff") = .some (s2ba "", .Constr 200 [.Map [(.I 1, .I 2)]]) := by native_decide

-- Reference fixtures: golden CBOR vectors for the shapes this PR touches (empty containers, empty
-- bytestring, negative bignums, tag-102 indices, nesting). Each pins `encodeData` to fixed bytes
-- and `decodeData` to invert them. The bytes are the canonical CBOR encoding mandated by the
-- reference (`Data.hs` / cborg / RFC 8949), hand-verifiable byte by byte, so the encode direction
-- is a genuine anchor and not a self-referential round-trip.
-- emptyList
example : encodeData (.List []) = .some "\x80" := by native_decide
example : decodeData (s2ba "\x80") = .some (s2ba "", .List []) := by native_decide
-- emptyConstr0
example : encodeData (.Constr 0 []) = .some "\xd8\x79\x80" := by native_decide
example : decodeData (s2ba "\xd8\x79\x80") = .some (s2ba "", .Constr 0 []) := by native_decide
-- emptyConstr5
example : encodeData (.Constr 5 []) = .some "\xd8\x7e\x80" := by native_decide
example : decodeData (s2ba "\xd8\x7e\x80") = .some (s2ba "", .Constr 5 []) := by native_decide
-- emptyB
example : encodeData (.B { data := "" }) = .some "\x40" := by native_decide
example : decodeData (s2ba "\x40") = .some (s2ba "", .B { data := "" }) := by native_decide
-- mapEmptyB
example : encodeData (.Map [(.B { data := "" }, .I 0)]) = .some "\xa1\x40\x00" := by native_decide
example : decodeData (s2ba "\xa1\x40\x00") = .some (s2ba "", .Map [(.B { data := "" }, .I 0)]) := by native_decide
-- negBignum64
example : encodeData (.I (-(2 ^ 64 + 1))) = .some "\xc3\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00" := by native_decide
example : decodeData (s2ba "\xc3\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00") = .some (s2ba "", .I (-(2 ^ 64 + 1))) := by native_decide
-- negBignum128
example : encodeData (.I (-(2 ^ 128))) = .some "\xc3\x50\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff" := by native_decide
example : decodeData (s2ba "\xc3\x50\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff") = .some (s2ba "", .I (-(2 ^ 128))) := by native_decide
-- constr128
example : encodeData (.Constr 128 []) = .some "\xd8\x66\x82\x18\x80\x80" := by native_decide
example : decodeData (s2ba "\xd8\x66\x82\x18\x80\x80") = .some (s2ba "", .Constr 128 []) := by native_decide
-- constrBig (2^63-1)
example : encodeData (.Constr (2 ^ 63 - 1) [.I 1]) = .some "\xd8\x66\x82\x1b\x7f\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff" := by native_decide
example : decodeData (s2ba "\xd8\x66\x82\x1b\x7f\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff") = .some (s2ba "", .Constr (2 ^ 63 - 1) [.I 1]) := by native_decide
-- constrMax (2^64-1, the largest in-range Word64 index)
example : encodeData (.Constr (2 ^ 64 - 1) [.I 1]) = .some "\xd8\x66\x82\x1b\xff\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff" := by native_decide
example : decodeData (s2ba "\xd8\x66\x82\x1b\xff\xff\xff\xff\xff\xff\xff\xff\x9f\x01\xff") = .some (s2ba "", .Constr (2 ^ 64 - 1) [.I 1]) := by native_decide
-- nested
example : encodeData (.Constr 0 [.List [], .I 5]) = .some "\xd8\x79\x9f\x80\x05\xff" := by native_decide
example : decodeData (s2ba "\xd8\x79\x9f\x80\x05\xff") = .some (s2ba "", .Constr 0 [.List [], .I 5]) := by native_decide
-- mapKV
example : encodeData (.Map [(.I 0, .I 1)]) = .some "\xa1\x00\x01" := by native_decide
example : decodeData (s2ba "\xa1\x00\x01") = .some (s2ba "", .Map [(.I 0, .I 1)]) := by native_decide
-- listII
example : encodeData (.List [.I 1, .I 2]) = .some "\x9f\x01\x02\xff" := by native_decide
example : decodeData (s2ba "\x9f\x01\x02\xff") = .some (s2ba "", .List [.I 1, .I 2]) := by native_decide

end PlutusCore.Cbor
