import Cryptograph.Integer
import Cryptograph.String

/-!
# Native-backed SHA-256 (libsodium)

Mirrors the surface of `Cryptograph.Sha2.Sha256` so call-sites can swap
backends by changing `import` / `open`. The C symbol
`lean_plutus_sha2_256` lives in `Cryptograph/FFI/c/lean_plutus_hash.c`.
-/

namespace Cryptograph.FFI.Sha2.Sha256

open Cryptograph.Integer

@[extern "lean_plutus_sha2_256"]
opaque hashBytes_bytes (input : @& ByteArray) : ByteArray

private def toBA (xs : List UInt8) : ByteArray :=
  xs.foldl (fun acc b => acc.push b) (ByteArray.emptyWithCapacity xs.length)

def hashBytes (input : List UInt8) : List UInt8 :=
  (hashBytes_bytes (toBA input)).toList

def hashMessage (input : List UInt8) : Vector UInt32 8 :=
  let ba := hashBytes_bytes (toBA input)
  let w (i : Nat) : UInt32 :=
    UInt32.ofUInt8BE #v[ba.get! (4*i), ba.get! (4*i+1), ba.get! (4*i+2), ba.get! (4*i+3)]
  #v[w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7]

def hash (input : String) : String :=
  Cryptograph.String.uint8ListToHex (hashBytes input.toUTF8.toList)

end Cryptograph.FFI.Sha2.Sha256
