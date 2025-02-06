import PlutusCore.ByteString
import PlutusCore.Integer

namespace PlutusCore.Bitwise
open PlutusCore.ByteString PlutusCore.Integer

/-! ## Formalisation for PlutusCore Logical and Bitwise builtin functions on ByteString. -/

namespace PlutusCore.BitwiseInternal

-- TODO: integerToByteString : Bool → Integer → Integer → Except String ByteString
-- TODO: byteStringToInteger : Bool → ByteString → Integer
-- TODO: andByteString : Bool → ByteString → ByteString → ByteString
-- TODO: orByteString : Bool → ByteString → ByteSgtring → ByteString
-- TODO: xorByteString : Bool → ByteString → ByteString → ByteString
-- TODO: complementByteString : ByteString → ByteString
-- TODO: shiftByteString : ByteString → Integer → ByteString
-- TODO: rotateByteString : ByteString → Integer → ByteString
-- TODO: countSetBits : ByteString → Integer
-- TODO: findFirstSetBit : ByteString → Integer
-- TODO: readBit : ByteString → Integer → Except String Bool
-- TODO: writeBits : ByteString → List Integer → Bool → Except String ByteString
-- TODO: replicateByte : Integer → Integer → Except String ByteString

end PlutusCore.BitwiseInternal
-- TODO: add export list

end PlutusCore.Bitwise

