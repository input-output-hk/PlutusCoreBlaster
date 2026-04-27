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
opaque verifyEd25519Signature (publicKey message signature : ByteString) : Except String Bool :=
  let pk  := String.toByteList publicKey.data
  let msg := String.toByteList message.data
  let sig := String.toByteList signature.data
  if pk.length  ≠ 32 then .error "verifyEd25519Signature: pk must be 32 bytes"
  else if sig.length ≠ 64 then .error "verifyEd25519Signature: sig must be 64 bytes"
  else .ok (Signature.verify pk msg sig)

end Internal

export Internal
  (
    verifyEd25519Signature
  )

end PlutusCore.Crypto.Ed25519
