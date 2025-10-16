import PlutusCore.Cbor.Basic

open PlutusCore.Cbor.CborInternal

example : e₈ 7234295460216005990 = "deadbeef".toList := rfl

example : splitToChunks "" = [] := by simp [splitToChunks]

example : splitToChunks "1234567890123456789012345678901234567890123456789012345678901234" =
  [ "1234567890123456789012345678901234567890123456789012345678901234" ] := by simp [splitToChunks]

example : splitToChunks  "12345678901234567890123456789012345678901234567890123456789012345" =
  [ "1234567890123456789012345678901234567890123456789012345678901234"
  , "5"
  ] := by simp [splitToChunks]

example : splitToChunks "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
  [ "1234567890123456789012345678901234567890123456789012345678901234"
  , "1234567890123456789012345678901234567890123456789012345678901234"
  , "56"
  ] := by simp [splitToChunks]

example : encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234" =
  .some ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234") := by simp [encodeBytestring, splitToChunks, encodeBytestringChunk, encodeHead]

example : encodeBytestring "12345678901234567890123456789012345678901234567890123456789012345" =
  .some ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x41"     ++ "5"
         ++ "\xFF") := by simp [encodeBytestring, splitToChunks, encodeBytestringChunk, encodeHead, encodeIndef]

example : encodeBytestring "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456" =
  .some ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x42"     ++ "56"
         ++ "\xFF") := by simp [encodeBytestring, splitToChunks, encodeBytestringChunk, encodeHead, encodeIndef]

example : encodeData (.I 12) = .some "\x0c"     := by simp [encodeData, encodeInt, encodeHead]
example : encodeData (.I 42) = .some "\x18\x2a" := by simp [encodeData, encodeInt, encodeHead]

example :
    encodeData (
      .Constr 0 [
        .Constr 0 [.I 1284531],
        .I 1739713998000
      ]
    ) = .some "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff" := by
          simp [encodeData, encodeCtag, encodeHead, encodeInt, encodeIndef, String.singleton, Char.ofNat, Nat.isValidChar, String.push]

example :
  encodeData (
    .Constr 0 [
      .I 144375414,
      .I 22710,
      .I 4387720097
    ]
  ) = .some "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff" := by
          simp [encodeData, encodeCtag, encodeHead, encodeInt, encodeIndef, String.singleton, Char.ofNat, Nat.isValidChar, String.push]
