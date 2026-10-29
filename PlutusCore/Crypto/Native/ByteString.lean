import PlutusCore.ByteString.Basic

namespace PlutusCore.Crypto.Native

open PlutusCore.ByteString (ByteString)

/-- Plutus stores one byte per character, including characters above ASCII. Hashing UTF-8
would change every byte ≥ 128. Match the reference's `Char.toUInt8` even for arbitrary strings. -/
def toBytes (input : ByteString) : ByteArray :=
  ⟨(input.data.data.map Char.toUInt8).toArray⟩

def fromBytes (input : ByteArray) : ByteString :=
  ⟨String.mk (input.toList.map Char.ofUInt8)⟩

end PlutusCore.Crypto.Native
