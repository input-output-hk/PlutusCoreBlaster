import Cryptograph.String

/-!
# Native-backed RIPEMD-160 (vendored crypton cbits)

Mirrors the surface of `Cryptograph.Ripemd.Ripemd160` so call-sites can
swap backends by changing `import` / `open`. The C symbol
`lean_plutus_ripemd_160` lives in `Cryptograph/FFI/c/lean_plutus_hash.c`.
-/

namespace Cryptograph.FFI.Ripemd.Ripemd160

@[extern "lean_plutus_ripemd_160"]
opaque ripemd160_bytes (input : @& ByteArray) : ByteArray

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

def ripemd160 (input : List UInt8) : List UInt8 :=
  (ripemd160_bytes (toBA input)).toList

def ripemd160_hash (input : String) : String :=
  Cryptograph.String.uint8ListToHex (ripemd160 input.toUTF8.toList)

end Cryptograph.FFI.Ripemd.Ripemd160
