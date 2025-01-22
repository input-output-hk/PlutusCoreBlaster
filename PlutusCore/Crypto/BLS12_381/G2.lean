import PlutusCore.ByteString
import PlutusCore.Integer

namespace PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Integer PlutusCore.ByteString

/-! ## Formalisation for PlutusCore BLS12_381_G2_Element representation and builtin functions. -/

namespace PlutusCore.Crypto.BLS12_381.G2Internal

-- TODO: BLS12_381_G2_Element

-- TODO bls12_381_G2_add : BLS12_381_G2_Element → BLS12_381_G2_Element → BLS12_381_G2_Element
-- TODO bls12_381_G2_neg : BLS12_381_G2_Element → BLS12_381_G2_Element
-- TODO bls12_381_G2_scalarMul : Integer → BLS12_381_G2_Element → BLS12_381_G2_Element
-- TODO bls12_381_G2_equal : BLS12_381_G2_Element → BLS12_381_G2_Element → Bool
-- TODO bls12_381_G2_hashToGroup : ByteString → ByteString → Except String BLS12_381_G2_Element
-- TODO bls12_381_G2_compress : BLS12_381_G2_Element → ByteString
-- TODO bls12_381_G2_uncompress : ByteString → Except String BLS12_381_G2_Element

end PlutusCore.Crypto.BLS12_381.G2Internal
-- TODO: add export

end PlutusCore.Crypto.BLS12_381.G2
