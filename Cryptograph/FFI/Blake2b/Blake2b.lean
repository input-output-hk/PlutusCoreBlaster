import Cryptograph.String

/-!
# Native-backed Blake2b-224 / Blake2b-256 (libsodium)

Mirrors the surface of `Cryptograph.Blake2b.Blake2b` so call-sites can
swap backends by changing `import` / `open`. The C symbols
`lean_plutus_blake2b_224` and `lean_plutus_blake2b_256` live in
`Cryptograph/FFI/c/lean_plutus_hash.c`.
-/

namespace Cryptograph.FFI.Blake2b.Blake2b

@[extern "lean_plutus_blake2b_256"]
opaque blake2b_256_bytes (input : @& ByteArray) : ByteArray

@[extern "lean_plutus_blake2b_224"]
opaque blake2b_224_bytes (input : @& ByteArray) : ByteArray

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

def blake2b_256 (input : List UInt8) : List UInt8 :=
  (blake2b_256_bytes (toBA input)).toList

def blake2b_224 (input : List UInt8) : List UInt8 :=
  (blake2b_224_bytes (toBA input)).toList

def blake2b_256_hash (input : String) : String :=
  Cryptograph.String.uint8ListToHex (blake2b_256 input.toUTF8.toList)

def blake2b_224_hash (input : String) : String :=
  Cryptograph.String.uint8ListToHex (blake2b_224 input.toUTF8.toList)

end Cryptograph.FFI.Blake2b.Blake2b
