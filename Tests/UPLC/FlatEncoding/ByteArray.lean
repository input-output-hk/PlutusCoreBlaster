import PlutusCore.UPLC.FlatEncoding.ByteArray

open PlutusCore.UPLC.FlatEncoding
open PlutusCore.UPLC.FlatEncoding.Internal

-- Compare the packed reader with the independent list reader over all byte
-- values, representative following bytes, every bit offset and EOF boundary.
#guard (List.range 256).all (fun first => [0, 1, 127, 128, 255].all (fun second =>
  let bytes := ByteArray.mk #[first.toUInt8, second.toUInt8]
  let bits := byteToBits (Char.ofNat first) ++ byteToBits (Char.ofNat second)
  (List.range 19).all (fun pos => (List.range 9).all (fun width =>
    let expected := (fun (_, n) => (pos + width, n)) <$> decodeFixedNat width (bits.drop pos)
    ByteDecoder.fixed bytes width pos == expected))))
