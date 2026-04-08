import Cryptograph.Secp256k1.ECDSA
import Cryptograph.Secp256k1.Schnorr
import Cryptograph.Secp256k1.Point
import Cryptograph.String
import PlutusCore.ByteString.Basic

namespace PlutusCore.Crypto.Secp256k1
open PlutusCore.ByteString
open Cryptograph.Secp256k1
open Cryptograph.Secp256k1.Point
open Cryptograph.String

/-! ## Formalisation for PlutusCore Secp256k1 verification builtin functions. -/

namespace Internal

-- ECDSA secp256k1 signature verification.
-- pk: 33 bytes (compressed), msg: 32 bytes (hash), sig: 64 bytes (compact r||s).
-- Returns .error for invalid lengths or unparseable key/sig (→ EvaluationError in CEK).
opaque verifyEcdsaSecp256k1Signature (publicKey message signature : ByteString) : Except String Bool :=
  let pk  := String.toByteList publicKey.data
  let msg := String.toByteList message.data
  let sig := String.toByteList signature.data
  if pk.length  ≠ 33 then .error "verifyEcdsaSecp256k1Signature: pk must be 33 bytes"
  else if msg.length ≠ 32 then .error "verifyEcdsaSecp256k1Signature: msg must be 32 bytes"
  else if sig.length ≠ 64 then .error "verifyEcdsaSecp256k1Signature: sig must be 64 bytes"
  else
    -- Per Plutus spec: r or s equal to 0 or ≥ curveOrder is an evaluation error (not False)
    let r := ECDSA.bytesToNat (sig.take 32)
    let s := ECDSA.bytesToNat (sig.drop 32)
    if r = 0 || r ≥ ECDSA.curveOrder then .error "verifyEcdsaSecp256k1Signature: r out of range"
    else if s = 0 || s ≥ ECDSA.curveOrder then .error "verifyEcdsaSecp256k1Signature: s out of range"
    else match Secp256k1Point.decompress pk with
    | none   => .error "verifyEcdsaSecp256k1Signature: invalid public key"
    | some _ => .ok (ECDSA.verify pk msg sig)

-- Schnorr secp256k1 signature verification (BIP-340).
-- pk: 32 bytes (x-only), msg: any length, sig: 64 bytes.
-- Returns .error for invalid lengths or unparseable key (→ EvaluationError in CEK).
opaque verifySchnorrSecp256k1Signature (publicKey message signature : ByteString) : Except String Bool :=
  let pk  := String.toByteList publicKey.data
  let msg := String.toByteList message.data
  let sig := String.toByteList signature.data
  if pk.length  ≠ 32 then .error "verifySchnorrSecp256k1Signature: pk must be 32 bytes"
  else if sig.length ≠ 64 then .error "verifySchnorrSecp256k1Signature: sig must be 64 bytes"
  else match Schnorr.liftX pk with
  | none   => .error "verifySchnorrSecp256k1Signature: invalid public key"
  | some _ => .ok (Schnorr.verify pk msg sig)

end Internal

export Internal
  (
    verifyEcdsaSecp256k1Signature
    verifySchnorrSecp256k1Signature
  )

end PlutusCore.Crypto.Secp256k1
