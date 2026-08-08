import PlutusCore.UPLC.CostModels
import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/31
--
-- `constSize` must count 8-byte words (matching ExMemoryUsage.hs: G1 = 18
-- words, G2 = 36 words), not EIP-2537 compressed-serialization byte lengths
-- (48/96). The point's specific coordinates are irrelevant to `constSize`,
-- so `default` (the point at infinity) is a fine stand-in.
namespace Tests.Issues.Issue31

open PlutusCore.UPLC.Term (Const)
open PlutusCore.UPLC.CostModels (constSize)
open PlutusCore.Crypto.BLS12_381.G1 (BLS12_381_G1_Element)
open PlutusCore.Crypto.BLS12_381.G2 (BLS12_381_G2_Element)

example : constSize (Const.Bls12_381_G1_element (default : BLS12_381_G1_Element)) = 144 := by
  native_decide

example : constSize (Const.Bls12_381_G2_element (default : BLS12_381_G2_Element)) = 288 := by
  native_decide

end Tests.Issues.Issue31
