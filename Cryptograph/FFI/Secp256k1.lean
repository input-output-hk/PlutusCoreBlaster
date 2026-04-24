/-!
# Native-backed secp256k1 signature verification (ECDSA + Schnorr)

Binds the C shims in `Cryptograph/FFI/c/lean_plutus_secp256k1.c`,
which call libsecp256k1 through the same set of symbols that
`Cardano.Crypto.SECP256K1.C` imports. Plutus wire formats:

* ECDSA:   publicKey 33B compressed SEC1, message 32B (pre-hashed),
           signature 64B compact (r ‖ s big-endian).
* Schnorr: publicKey 32B x-only, signature 64B, message any length.

Any parse or size failure yields `false`.
-/

namespace Cryptograph.FFI.Secp256k1

@[extern "lean_plutus_ecdsa_verify"]
opaque verifyEcdsa_bytes
    (publicKey : @& ByteArray)
    (message   : @& ByteArray)
    (signature : @& ByteArray)
    : Bool

@[extern "lean_plutus_schnorr_verify"]
opaque verifySchnorr_bytes
    (publicKey : @& ByteArray)
    (message   : @& ByteArray)
    (signature : @& ByteArray)
    : Bool

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

def verifyEcdsa (publicKey message signature : List UInt8) : Bool :=
  verifyEcdsa_bytes (toBA publicKey) (toBA message) (toBA signature)

def verifySchnorr (publicKey message signature : List UInt8) : Bool :=
  verifySchnorr_bytes (toBA publicKey) (toBA message) (toBA signature)

end Cryptograph.FFI.Secp256k1
