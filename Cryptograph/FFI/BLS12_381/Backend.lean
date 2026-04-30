import Cryptograph.BLS12_381.Backend
import Cryptograph.FFI.BLS12_381.Surface

/-!
# FFI-backend instance of `Cryptograph.BLS12_381.BlsBackend`

Provides the native instance separately from the typeclass module so
modules that only need the pure backend do not need to link the C
shims.
-/

namespace Cryptograph.FFI.BLS12_381

open Cryptograph.BLS12_381 (BlsBackend)

instance ffiBackend : BlsBackend G1Point G2Point MlResult where
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

end Cryptograph.FFI.BLS12_381
