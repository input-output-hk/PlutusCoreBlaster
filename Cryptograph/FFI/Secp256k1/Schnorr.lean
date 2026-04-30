/-!
# Native-backed secp256k1 Schnorr verification (libsecp256k1)

Mirrors the surface of `Cryptograph.Secp256k1.Schnorr` so call-sites
can swap backends by changing `import` / `open`. Plutus wire format:
publicKey 32B x-only, signature 64B, message any length. Any parse or
size failure yields `false`.
-/

namespace Cryptograph.FFI.Secp256k1.Schnorr

@[extern "lean_plutus_schnorr_verify"]
opaque verify_bytes
    (publicKey : @& ByteArray)
    (message   : @& ByteArray)
    (signature : @& ByteArray)
    : Bool

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

def verify (publicKey message signature : List UInt8) : Bool :=
  verify_bytes (toBA publicKey) (toBA message) (toBA signature)

end Cryptograph.FFI.Secp256k1.Schnorr
