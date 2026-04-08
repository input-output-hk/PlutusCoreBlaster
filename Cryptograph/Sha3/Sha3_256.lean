import Cryptograph.Keccak.Keccak256

namespace Cryptograph.Sha3.Sha3_256

/-! ## SHA3-256 Hash Implementation-/

-- SHA3-256 hash function for byte lists
def hashBytes (input : List UInt8) : List UInt8 :=
  Cryptograph.Keccak.Keccak256.sha3_256_hashBytes input

-- SHA3-256 hash function for strings
def hash (input : String) : String :=
  Cryptograph.Keccak.Keccak256.sha3_256_hash input

end Cryptograph.Sha3.Sha3_256
