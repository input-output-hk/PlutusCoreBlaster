import Cryptograph.FFI.Native
import PlutusCore.Crypto.Native.ByteString
import Cryptograph.Sha2
import Cryptograph.Sha3
import Cryptograph.Blake2b
import Cryptograph.Keccak
import Cryptograph.Ripemd
import Cryptograph.String

import PlutusCore.ByteString.Basic

namespace PlutusCore.Crypto.Hash

open Cryptograph.Sha2
open Cryptograph.Sha3
open Cryptograph.Blake2b
open Cryptograph.Keccak
open Cryptograph.Ripemd
open Cryptograph.String
open PlutusCore.ByteString

/-! ## Formalisation for PlutusCore hash builtin functions. -/

namespace Internal

def sha2_256Reference (x : ByteString) : ByteString :=
  let hash := Sha256.hashMessage (x.data.data.map Char.toUInt8)
  let bytes := (Vector.toList hash).flatMap (fun (w : UInt32) =>
    [((w >>> 24) &&& 0xFF).toUInt8,
     ((w >>> 16) &&& 0xFF).toUInt8,
     ((w >>> 8) &&& 0xFF).toUInt8,
     (w &&& 0xFF).toUInt8])
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

def sha3_256Reference (x : ByteString) : ByteString :=
  let bytes := Sha3_256.hashBytes (x.data.data.map Char.toUInt8)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

def blake2b_224Reference (x : ByteString) : ByteString :=
  let bytes := Blake2b.blake2b_224 (x.data.data.map Char.toUInt8)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

def blake2b_256Reference (x : ByteString) : ByteString :=
  let bytes := Blake2b.blake2b_256 (x.data.data.map Char.toUInt8)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

def keccak_256Reference (x : ByteString) : ByteString :=
  let bytes := Keccak256.hashBytes (x.data.data.map Char.toUInt8)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩

def ripemd_160Reference (x : ByteString) : ByteString :=
  let bytes := Ripemd160.ripemd160 (x.data.data.map Char.toUInt8)
  ⟨⟨Char.ofUInt8 <$> bytes⟩⟩


private def sha2_256Native (x : ByteString) : ByteString :=
  Native.fromBytes (Cryptograph.FFI.Native.sha2_256 (Native.toBytes x))

@[implemented_by sha2_256Native]
opaque sha2_256 (x : ByteString) : ByteString := sha2_256Reference x

private def sha3_256Native (x : ByteString) : ByteString :=
  Native.fromBytes (Cryptograph.FFI.Native.sha3_256 (Native.toBytes x))

@[implemented_by sha3_256Native]
opaque sha3_256 (x : ByteString) : ByteString := sha3_256Reference x

private def blake2b_224Native (x : ByteString) : ByteString :=
  Native.fromBytes (Cryptograph.FFI.Native.blake2b_224 (Native.toBytes x))

@[implemented_by blake2b_224Native]
opaque blake2b_224 (x : ByteString) : ByteString := blake2b_224Reference x

private def blake2b_256Native (x : ByteString) : ByteString :=
  Native.fromBytes (Cryptograph.FFI.Native.blake2b_256 (Native.toBytes x))

@[implemented_by blake2b_256Native]
opaque blake2b_256 (x : ByteString) : ByteString := blake2b_256Reference x

private def keccak_256Native (x : ByteString) : ByteString :=
  Native.fromBytes (Cryptograph.FFI.Native.keccak_256 (Native.toBytes x))

@[implemented_by keccak_256Native]
opaque keccak_256 (x : ByteString) : ByteString := keccak_256Reference x

private def ripemd_160Native (x : ByteString) : ByteString :=
  Native.fromBytes (Cryptograph.FFI.Native.ripemd_160 (Native.toBytes x))

@[implemented_by ripemd_160Native]
opaque ripemd_160 (x : ByteString) : ByteString := ripemd_160Reference x

end Internal

export Internal
  (
    sha2_256Reference
    sha3_256Reference
    blake2b_224Reference
    blake2b_256Reference
    keccak_256Reference
    ripemd_160Reference
    sha2_256
    sha3_256
    blake2b_224
    blake2b_256
    keccak_256
    ripemd_160
  )

end PlutusCore.Crypto.Hash
