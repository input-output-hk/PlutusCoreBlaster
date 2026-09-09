import Cryptograph.Sha2
import Cryptograph.Sha3
import Cryptograph.Keccak
import Cryptograph.Blake2b
import Cryptograph.Ripemd

import PlutusCore.Crypto.Hash

namespace PlutusCore.Crypto.Hash.Tests.AxiomsValidate

open Cryptograph.Sha2
open Cryptograph.Sha3
open Cryptograph.Keccak
open Cryptograph.Blake2b
open Cryptograph.Ripemd

/-- A 200-byte input, matching the conformance suite's `length_200` cases. -/
private def input200 : List UInt8 := List.replicate 200 0x61

example (x : List UInt8) : (Sha256.hashMessage x).toList.length = 8 := by simp

/-! ### The other five: sampled on the empty and the 200-byte input -/

example : (Sha3_256.hashBytes  []).length = 32 := by native_decide
example : (Keccak256.hashBytes []).length = 32 := by native_decide
example : (Blake2b.blake2b_256 []).length = 32 := by native_decide
example : (Blake2b.blake2b_224 []).length = 28 := by native_decide
example : (Ripemd160.ripemd160 []).length = 20 := by native_decide

example : (Sha3_256.hashBytes  input200).length = 32 := by native_decide
example : (Keccak256.hashBytes input200).length = 32 := by native_decide
example : (Blake2b.blake2b_256 input200).length = 32 := by native_decide
example : (Blake2b.blake2b_224 input200).length = 28 := by native_decide
example : (Ripemd160.ripemd160 input200).length = 20 := by native_decide

example : ¬ (Blake2b.blake2b_224 [] = (Blake2b.blake2b_256 []).take 28) := by native_decide

example : ¬ (Blake2b.blake2b_224 [0x61, 0x62, 0x63] = (Blake2b.blake2b_256 [0x61, 0x62, 0x63]).take 28) := by native_decide

end PlutusCore.Crypto.Hash.Tests.AxiomsValidate
