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
  byteArrayToByteString (Sha256.hashMessage (byteStringToByteArray x))

opaque sha3_256 (x : ByteString) : ByteString :=
  byteArrayToByteString (Sha3_256.hashBytes (byteStringToByteArray x))

opaque blake2b_224 (x : ByteString) : ByteString :=
  byteArrayToByteString (Blake2b.blake2b_224 (byteStringToByteArray x))

opaque blake2b_256 (x : ByteString) : ByteString :=
  byteArrayToByteString (Blake2b.blake2b_256 (byteStringToByteArray x))

opaque keccak_256 (x : ByteString) : ByteString :=
  byteArrayToByteString (Keccak256.hashBytes (byteStringToByteArray x))

opaque ripemd_160 (x : ByteString) : ByteString :=
  byteArrayToByteString (Ripemd160.ripemd160 (byteStringToByteArray x))

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
