import Cryptograph.FFI.Native
import PlutusCore.Crypto.Native.ByteString
import Cryptograph.Ed25519
import Cryptograph.String
import PlutusCore.ByteString.Basic

namespace PlutusCore.Crypto.Ed25519
open PlutusCore.ByteString
open Cryptograph.Ed25519
open Cryptograph.String

/-! ## Formalisation for PlutusCore Ed25519 verification builtin functions. -/

namespace Internal

-- Ed25519 signature verification (both V1 and V2 use the same implementation).
-- pk: 32 bytes, msg: any length, sig: 64 bytes.
-- Returns .error for invalid lengths (→ EvaluationError in CEK).
def verifyEd25519SignatureReference (publicKey message signature : ByteString) : Except String Bool :=
  let pk  := publicKey.data.data.map Char.toUInt8
  let msg := message.data.data.map Char.toUInt8
  let sig := signature.data.data.map Char.toUInt8
  if pk.length  ≠ 32 then .error "verifyEd25519Signature: pk must be 32 bytes"
  else if sig.length ≠ 64 then .error "verifyEd25519Signature: sig must be 64 bytes"
  else .ok (Signature.verify pk msg sig)

private def verifyEd25519SignatureNative (publicKey message signature : ByteString) : Except String Bool :=
  let pk := Native.toBytes publicKey
  let sig := Native.toBytes signature
  if pk.size ≠ 32 then .error "verifyEd25519Signature: pk must be 32 bytes"
  else if sig.size ≠ 64 then .error "verifyEd25519Signature: sig must be 64 bytes"
  else .ok (Cryptograph.FFI.Native.verifyEd25519 pk (Native.toBytes message) sig)

@[implemented_by verifyEd25519SignatureNative]
opaque verifyEd25519Signature (publicKey message signature : ByteString) : Except String Bool :=
  verifyEd25519SignatureReference publicKey message signature

end Internal

export Internal
  (
    verifyEd25519Signature
    verifyEd25519SignatureReference
  )

end PlutusCore.Crypto.Ed25519
