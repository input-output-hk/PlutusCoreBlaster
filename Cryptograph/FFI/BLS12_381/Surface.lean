import Cryptograph.FFI.BLS12_381.G1
import Cryptograph.FFI.BLS12_381.G2
import Cryptograph.FFI.BLS12_381.Pairing

/-!
# `List UInt8` / `Option` surface for the FFI BLS12-381 backend

The native bindings in `G1.lean`, `G2.lean`, `Pairing.lean` operate on
`ByteArray` and use `Except String` for parse failures. This file
re-exposes them in the same shape that
`Cryptograph.BLS12_381.Surface` uses for the pure backend, so
call-sites can swap pure ↔ FFI by changing one `import` / `open`.

The byte-typed declarations are still available under their original
names with a `_bytes` suffix (`compress_bytes`, `uncompress_bytes`,
`hashToGroup_bytes`, `scalarMul_bytes`) — reach for those when
zero-copy across the FFI matters.
-/

namespace Cryptograph.FFI.BLS12_381

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

namespace G1

def scalarMul (scalar : List UInt8) (p : G1Point) : G1Point :=
  scalarMul_bytes (toBA scalar) p

def compress (p : G1Point) : List UInt8 :=
  (compress_bytes p).toList

def uncompress (bytes : List UInt8) : Option G1Point :=
  match uncompress_bytes (toBA bytes) with
  | .ok p    => some p
  | .error _ => none

def hashToGroup (msg dst : List UInt8) : Option G1Point :=
  some (hashToGroup_bytes (toBA msg) (toBA dst))

end G1

namespace G2

def scalarMul (scalar : List UInt8) (p : G2Point) : G2Point :=
  scalarMul_bytes (toBA scalar) p

def compress (p : G2Point) : List UInt8 :=
  (compress_bytes p).toList

def uncompress (bytes : List UInt8) : Option G2Point :=
  match uncompress_bytes (toBA bytes) with
  | .ok p    => some p
  | .error _ => none

def hashToGroup (msg dst : List UInt8) : Option G2Point :=
  some (hashToGroup_bytes (toBA msg) (toBA dst))

end G2

end Cryptograph.FFI.BLS12_381
