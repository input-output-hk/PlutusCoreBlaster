/-!
# Native-backed Ed25519 signature verification

Binds `lean_plutus_ed25519_verify` in
`Cryptograph/FFI/c/lean_plutus_ed25519.c`, which invokes
`crypto_sign_ed25519_verify_detached` from libsodium — the same symbol
that `Cardano.Crypto.DSIGN.Ed25519` reaches via `foreign import ccall`.

Plutus-compatible semantics: returns `false` on any size mismatch
(publicKey must be 32 bytes, signature must be 64 bytes) rather than
raising an error.
-/

namespace Cryptograph.FFI.Ed25519

@[extern "lean_plutus_ed25519_verify"]
opaque verify_bytes
    (publicKey : @& ByteArray)
    (message   : @& ByteArray)
    (signature : @& ByteArray)
    : Bool

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

/-- `List UInt8` wrapper matching `Cryptograph.Ed25519.Signature.verify`. -/
def verify (publicKey message signature : List UInt8) : Bool :=
  verify_bytes (toBA publicKey) (toBA message) (toBA signature)

end Cryptograph.FFI.Ed25519
