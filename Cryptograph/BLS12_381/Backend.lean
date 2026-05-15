import Cryptograph.BLS12_381.Surface

/-!
# Backend-agnostic interface for BLS12-381

`BlsBackend` abstracts the three carrier types and the operation set
shared by the pure (`Cryptograph.BLS12_381`) and native
(`Cryptograph.FFI.BLS12_381`) backends. Backend-agnostic code takes
`[BlsBackend G1 G2 Ml]` as an instance argument; the user picks the
backend at the call site by which instance is in scope.

The pure-backend instance is registered here. The FFI-backend instance
lives in `Cryptograph.FFI.BLS12_381.Backend` (separate file so the
typeclass module itself does not pull in the native link
dependencies).
-/

namespace Cryptograph.BLS12_381

class BlsBackend (G1 : outParam Type) (G2 : outParam Type) (Ml : outParam Type) where
  g1Add         : G1 → G1 → G1
  g1Neg         : G1 → G1
  g1ScalarMul   : List UInt8 → G1 → G1
  g1Equal       : G1 → G1 → Bool
  g1Compress    : G1 → List UInt8
  g1Uncompress  : List UInt8 → Option G1
  g1HashToGroup : List UInt8 → List UInt8 → Option G1
  g2Add         : G2 → G2 → G2
  g2Neg         : G2 → G2
  g2ScalarMul   : List UInt8 → G2 → G2
  g2Equal       : G2 → G2 → Bool
  g2Compress    : G2 → List UInt8
  g2Uncompress  : List UInt8 → Option G2
  g2HashToGroup : List UInt8 → List UInt8 → Option G2
  millerLoop    : G1 → G2 → Ml
  mulMlResult   : Ml → Ml → Ml
  finalVerify   : Ml → Ml → Bool

instance pureBackend : BlsBackend G1Point G2Point MlResult where
  g1Add         := G1.add
  g1Neg         := G1.neg
  g1ScalarMul   := G1.scalarMul
  g1Equal       := G1.equal
  g1Compress    := G1.compress
  g1Uncompress  := G1.uncompress
  g1HashToGroup := G1.hashToGroup
  g2Add         := G2.add
  g2Neg         := G2.neg
  g2ScalarMul   := G2.scalarMul
  g2Equal       := G2.equal
  g2Compress    := G2.compress
  g2Uncompress  := G2.uncompress
  g2HashToGroup := G2.hashToGroup
  millerLoop    := Pairing.millerLoop
  mulMlResult   := Pairing.mulMlResult
  finalVerify   := Pairing.finalVerify

end Cryptograph.BLS12_381
