import PlutusCore.ByteString
import PlutusCore.Integer

namespace PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Integer PlutusCore.ByteString

/-! ## Formalisation for PlutusCore BLS12_381_G1_Element representation and builtin functions. -/

namespace PlutusCore.Crypto.BLS12_381.G1Internal

-- TODO: BLS12_381_G1_Element

-- TODO bls12_381_G1_add : BLS12_381_G1_Element → BLS12_381_G1_Element → BLS12_381_G1_Element
-- TODO bls12_381_G1_neg : BLS12_381_G1_Element → BLS12_381_G1_Element
-- TODO bls12_381_G1_scalarMul : Integer → BLS12_381_G1_Element → BLS12_381_G1_Element
-- TODO bls12_381_G1_equal : BLS12_381_G1_Element → BLS12_381_G1_Element → Bool
-- TODO bls12_381_G1_hashToGroup : ByteString → ByteString → Except String BLS12_381_G1_Element
-- TODO bls12_381_G1_compress : BLS12_381_G1_Element → ByteString
-- TODO bls12_381_G1_uncompress : ByteString → Except String BLS12_381_G1_Element

end PlutusCore.Crypto.BLS12_381.G1Internal

-- TODO: add export

end PlutusCore.Crypto.BLS12_381.G1
