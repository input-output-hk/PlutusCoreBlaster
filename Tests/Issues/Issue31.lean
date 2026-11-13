import Blaster
import PlutusCore.UPLC.CostModels
import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/31
--
-- `constSize` must count 8-byte words of blst's in-memory representation,
-- matching ExMemoryUsage.hs (`memSizeBytes / 8`): G1 = 18 words, G2 = 36
-- words, MlResult = 72 words. It must not count the compressed serialization
-- lengths (48/96 bytes for G1/G2) or raw bytes (576 for MlResult). The value
-- itself is irrelevant to `constSize`, so `default` (the point at infinity)
-- and `none` are fine stand-ins.
namespace Tests.Issue31

open PlutusCore.UPLC.Term (Const)
open PlutusCore.UPLC.CostModels (constSize)
open PlutusCore.Crypto.BLS12_381.G1 (BLS12_381_G1_Element)
open PlutusCore.Crypto.BLS12_381.G2 (BLS12_381_G2_Element)

set_option warn.sorry false

example : constSize (Const.Bls12_381_G1_element (default : BLS12_381_G1_Element)) = 18 := by
  blaster

example : constSize (Const.Bls12_381_G2_element (default : BLS12_381_G2_Element)) = 36 := by
  blaster

example : constSize (Const.Bls12_381_MlResult none) = 72 := by
  blaster

end Tests.Issue31
