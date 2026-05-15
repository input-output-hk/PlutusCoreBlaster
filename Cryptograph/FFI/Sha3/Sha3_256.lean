import Cryptograph.String

/-!
# Native-backed SHA3-256 (vendored crypton cbits)

Mirrors the surface of `Cryptograph.Sha3.Sha3_256` so call-sites can
swap backends by changing `import` / `open`. The C symbol
`lean_plutus_sha3_256` lives in `Cryptograph/FFI/c/lean_plutus_hash.c`.
-/

namespace Cryptograph.FFI.Sha3.Sha3_256

@[extern "lean_plutus_sha3_256"]
opaque hashBytes_bytes (input : @& ByteArray) : ByteArray

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

def hashBytes (input : List UInt8) : List UInt8 :=
  (hashBytes_bytes (toBA input)).toList

def hash (input : String) : String :=
  Cryptograph.String.uint8ListToHex (hashBytes input.toUTF8.toList)

end Cryptograph.FFI.Sha3.Sha3_256
