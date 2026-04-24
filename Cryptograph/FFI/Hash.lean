/-!
# Native-backed hash primitives for the Plutus UPLC hash builtins

Each `@[extern]` declaration below names the exact C symbol in
`Cryptograph/FFI/c/lean_plutus_hash.c`. Those shims in turn call the
same upstream C functions that the Haskell Plutus evaluator uses
(libsodium for SHA2-256 / Blake2b; vendored crypton cbits for
SHA3-256, Keccak-256, RIPEMD-160).

The `*_bytes` functions take and return `ByteArray`. Thin
`List UInt8 → List UInt8` wrappers exist so call-sites written against
the pure `Cryptograph.*` API can swap implementations without a type
change.
-/

namespace Cryptograph.FFI.Hash

/-! ## ByteArray-typed externs (primary, zero-copy across FFI) -/

@[extern "lean_plutus_sha2_256"]
opaque sha2_256_bytes (input : @& ByteArray) : ByteArray

@[extern "lean_plutus_blake2b_256"]
opaque blake2b_256_bytes (input : @& ByteArray) : ByteArray

@[extern "lean_plutus_blake2b_224"]
opaque blake2b_224_bytes (input : @& ByteArray) : ByteArray

@[extern "lean_plutus_sha3_256"]
opaque sha3_256_bytes (input : @& ByteArray) : ByteArray

@[extern "lean_plutus_keccak_256"]
opaque keccak_256_bytes (input : @& ByteArray) : ByteArray

@[extern "lean_plutus_ripemd_160"]
opaque ripemd_160_bytes (input : @& ByteArray) : ByteArray

/-! ## `List UInt8` wrappers (API-compatible with pure Cryptograph) -/

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

private def ofBA (ba : ByteArray) : List UInt8 := ba.toList

def sha2_256    (input : List UInt8) : List UInt8 := ofBA (sha2_256_bytes    (toBA input))
def blake2b_256 (input : List UInt8) : List UInt8 := ofBA (blake2b_256_bytes (toBA input))
def blake2b_224 (input : List UInt8) : List UInt8 := ofBA (blake2b_224_bytes (toBA input))
def sha3_256    (input : List UInt8) : List UInt8 := ofBA (sha3_256_bytes    (toBA input))
def keccak_256  (input : List UInt8) : List UInt8 := ofBA (keccak_256_bytes  (toBA input))
def ripemd_160  (input : List UInt8) : List UInt8 := ofBA (ripemd_160_bytes  (toBA input))

end Cryptograph.FFI.Hash
