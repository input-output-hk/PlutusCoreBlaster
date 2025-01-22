import PlutusCore.ByteString
import PlutusCore.Integer

namespace PlutusCore.Crypto.BLS12_381.Pairing
open PlutusCore.Integer PlutusCore.ByteString

/-! ## Formalisation for PlutusCore BLS12_381_MlResult representation and builtin functions. -/

namespace PlutusCore.Crypto.BLS12_381.PairingInternal

-- TODO: BLS12_381_MlResult

-- TODO: bls12_381_millerLoop : BLS12_381_G1_Element → BLS12_381_G2_Element → BLS12_381_MlResult
-- TODO: bls12_381_mulMlResult : BLS12_381_MlResult → BLS12_381_MlResult → BLS12_381_MLResult
-- TODO: bls12_381_finalVerify : BLS12_381_MlResult → BLS12_381_MlResult → Bool

end PlutusCore.Crypto.BLS12_381.PairingInternal
-- TODO: add export

end PlutusCore.Crypto.BLS12_381.Pairing
