import Cryptograph.Sha2.Sha256
import Cryptograph.Sha3.Sha3_256
import Cryptograph.Blake2b
import Cryptograph.Keccak
import Cryptograph.Ripemd
import Cryptograph.Ed25519

/-! ByteArray bindings for native crypto. Every declaration has a Lean body; these bindings
add no crypto axioms. `extern` replaces compiled execution, without proving the C code correct.
The Plutus wrappers retain their pure reference implementations for differential testing. -/

namespace Cryptograph.FFI.Native

private def bytes (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

@[extern "lean_plutus_sha2_256"]
def sha2_256 (input : @& ByteArray) : ByteArray :=
  bytes ((Sha2.Sha256.hashMessage input.toList).toList.flatMap Integer.UInt32.toUInt8BE)

@[extern "lean_plutus_sha3_256"]
def sha3_256 (input : @& ByteArray) : ByteArray := bytes (Sha3.Sha3_256.hashBytes input.toList)

@[extern "lean_plutus_blake2b_256"]
def blake2b_256 (input : @& ByteArray) : ByteArray := bytes (Blake2b.blake2b_256 input.toList)

@[extern "lean_plutus_blake2b_224"]
def blake2b_224 (input : @& ByteArray) : ByteArray := bytes (Blake2b.blake2b_224 input.toList)

@[extern "lean_plutus_keccak_256"]
def keccak_256 (input : @& ByteArray) : ByteArray := bytes (Keccak.Keccak256.hashBytes input.toList)

@[extern "lean_plutus_ripemd_160"]
def ripemd_160 (input : @& ByteArray) : ByteArray := bytes (Ripemd.Ripemd160.ripemd160 input.toList)

@[extern "lean_plutus_ed25519_verify"]
def verifyEd25519 (pk msg sig : @& ByteArray) : Bool :=
  Ed25519.Signature.verify pk.toList msg.toList sig.toList

@[extern "lean_plutus_crypto_initialize"]
private def initializeCrypto : IO Unit := pure ()

builtin_initialize initializeCrypto

end Cryptograph.FFI.Native
