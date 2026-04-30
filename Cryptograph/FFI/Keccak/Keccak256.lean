import Cryptograph.String

/-!
# Native-backed Keccak-256 (vendored crypton cbits)

Mirrors the surface of `Cryptograph.Keccak.Keccak256` so call-sites can
swap backends by changing `import` / `open`. C symbols
`lean_plutus_keccak_256` and `lean_plutus_sha3_256` live in
`Cryptograph/FFI/c/lean_plutus_hash.c`.
-/

namespace Cryptograph.FFI.Keccak.Keccak256

@[extern "lean_plutus_keccak_256"]
opaque hashBytes_bytes (input : @& ByteArray) : ByteArray

@[extern "lean_plutus_sha3_256"]
opaque sha3_256_hashBytes_bytes (input : @& ByteArray) : ByteArray

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

def hashBytes (input : List UInt8) : List UInt8 :=
  (hashBytes_bytes (toBA input)).toList

def hash (input : String) : String :=
  Cryptograph.String.uint8ListToHex (hashBytes input.toUTF8.toList)

def sha3_256_hashBytes (input : List UInt8) : List UInt8 :=
  (sha3_256_hashBytes_bytes (toBA input)).toList

def sha3_256_hash (input : String) : String :=
  Cryptograph.String.uint8ListToHex (sha3_256_hashBytes input.toUTF8.toList)

end Cryptograph.FFI.Keccak.Keccak256
