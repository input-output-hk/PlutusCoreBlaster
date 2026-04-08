import Cryptograph.Sha2
import Cryptograph.Sha3
import Cryptograph.Blake2b
import Cryptograph.Keccak
import Cryptograph.Ripemd
import Cryptograph.String

import PlutusCore.ByteString.Basic

namespace PlutusCore.Crypto.Hash

open Cryptograph.Sha2
open Cryptograph.Sha3
open Cryptograph.Blake2b
open Cryptograph.Keccak
open Cryptograph.Ripemd
open Cryptograph.String
open PlutusCore.ByteString

/-! ## Formalisation for PlutusCore hash builtin functions. -/

namespace Internal

opaque sha2_256 (x : ByteString) : ByteString :=
  let hash := Sha256.hashMessage (String.toByteList x.data)
  let bytes := (Vector.toList hash).flatMap (fun (w : UInt32) =>
    [((w >>> 24) &&& 0xFF).toUInt8,
     ((w >>> 16) &&& 0xFF).toUInt8,
     ((w >>> 8) &&& 0xFF).toUInt8,
     (w &&& 0xFF).toUInt8])
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

opaque sha3_256 (x : ByteString) : ByteString :=
  let bytes := Sha3_256.hashBytes (String.toByteList x.data)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

opaque blake2b_224 (x : ByteString) : ByteString :=
  let bytes := Blake2b.blake2b_224 (String.toByteList x.data)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

opaque blake2b_256 (x : ByteString) : ByteString :=
  let bytes := Blake2b.blake2b_256 (String.toByteList x.data)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

opaque keccak_256 (x : ByteString) : ByteString :=
  let bytes := Keccak256.hashBytes (String.toByteList x.data)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

opaque ripemd_160 (x : ByteString) : ByteString :=
  let bytes := Ripemd160.ripemd160 (String.toByteList x.data)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

end Internal

export Internal
  (
    sha2_256
    sha3_256
    blake2b_224
    blake2b_256
    keccak_256
    ripemd_160
  )

end PlutusCore.Crypto.Hash
