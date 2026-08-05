import Cryptograph.BLS12_381.Basic

import PlutusCore.ByteString
import PlutusCore.Crypto.BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing

namespace PlutusCore.Crypto.BLS12_381.Axioms

namespace Internal

open Cryptograph.BLS12_381

open PlutusCore.ByteString
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Crypto.BLS12_381.Pairing

variable (a₁ b₁ c₁ : BLS12_381_G1_Element)
variable (a₂ b₂ c₂ : BLS12_381_G2_Element)
variable (m₁ m₂ m₃ : BLS12_381_MlResult)
variable (m n : Int)
variable (b : ByteString)

abbrev r : Int := .ofNat groupOrder

/- Identity elements -/
abbrev zeroG1 : BLS12_381_G1_Element := .infinity
abbrev zeroG2 : BLS12_381_G2_Element := .infinity

instance : Zero BLS12_381_G1_Element := ⟨zeroG1⟩
instance : Zero BLS12_381_G2_Element := ⟨zeroG2⟩

/- Group axioms.
   (G1,+,0,neg) and (G2,+,0,neg) are abelian groups. -/

axiom g1_add_assoc : (a₁ + b₁) + c₁ = a₁ + (b₁ + c₁)
axiom g1_add_comm  : a₁ + b₁ = b₁ + a₁
axiom g1_add_zero  : a₁ + 0 = a₁
axiom g1_add_neg   : a₁ + (-a₁) = 0

axiom g2_add_assoc : (a₂ + b₂) + c₂ = a₂ + (b₂ + c₂)
axiom g2_add_comm  : a₂ + b₂ = b₂ + a₂
axiom g2_add_zero  : a₂ + 0 = a₂
axiom g2_add_neg   : a₂ + (-a₂) = 0

/- Prime cyclic order r.
  Each Gᵢ ≅ ℤ/r via a fixed generator. This is what collapses all group
  reasoning to modular arithmetic. `dlogGi` is the discrete log into [0, r). -/

axiom g1_dlog : BLS12_381_G1_Element → Int
axiom g2_dlog : BLS12_381_G2_Element → Int

axiom g1_cyclic : a₁ = (g1_dlog a₁) * g1
axiom g2_cyclic : a₂ = (g2_dlog a₂) * g2

axiom g1_dlog_scalarMul : g1_dlog (n * g1) = n % r
axiom g2_dlog_scalarMul : g2_dlog (n * g2) = n % r

/- Order exactly r: the generator has order r. -/

theorem g1_order : r * g1 = 0 := by decide +native
theorem g2_order : r * g2 = 0 := by decide +native

/- Scalar-action laws (ℤ/r-module). -/

axiom g1_scalarMul_zero : 0 * a₁ = 0
axiom g1_scalarMul_one  : 1 * a₁ = a₁

axiom g1_scalarMul_add_scalar : (m + n) * a₁ = (m * a₁) + (n * a₁)
axiom g1_scalarMul_add_point  : n * (a₁ + b₁) = (n * a₁) + (n * b₁)
axiom g1_scalarMul_mul        : (m * n) * a₁ = m * (n * a₁)
axiom g1_scalarMul_mod        : (n % r) * a₁ = n * a₁
axiom g1_scalarMul_neg        : (-1) * a₁ = -a₁

axiom g2_scalarMul_zero : 0 * a₂ = 0
axiom g2_scalarMul_one  : 1 * a₂ = a₂

axiom g2_scalarMul_add_scalar : (m + n) * a₂ = (m * a₂) + (n * a₂)
axiom g2_scalarMul_add_point  : n * (a₂ + b₂) = (n * a₂) + (n * b₂)
axiom g2_scalarMul_mul        : (m * n) * a₂ = m * (n * a₂)
axiom g2_scalarMul_mod        : (n % r) * a₂ = n * a₂
axiom g2_scalarMul_neg        : (-1) * a₂ = -a₂

/- Bilinear pairing (THE IRREDUCIBLE CROSS-GROUP RULE).
   Modeled through an abstract target group `GT` (order r) and the abstract
   pairing `e : G1 → G2 → GT`. The link to the builtins is R5 (`pi`). -/

/- Abstract pairing target `G_T` (multiplicative, cyclic order r). -/
axiom GT : Type
axiom gtOne : GT
axiom gtMul : GT → GT → GT
axiom gtGen : GT  -- generator = e(g1,g2)
axiom gtPow : GT → Int → GT

noncomputable instance : One GT := ⟨gtOne⟩
noncomputable instance : Mul GT := ⟨gtMul⟩
noncomputable instance : HPow GT Int GT := ⟨gtPow⟩

/- The pairing itself. -/
axiom e : BLS12_381_G1_Element → BLS12_381_G2_Element → GT

axiom e_add_left  : e (a₁ + b₁) a₂ = (e a₁ a₂) * (e b₁ a₂)
axiom e_add_right : e a₁ (a₂ + b₂) = (e a₁ a₂) * (e a₁ b₂)

axiom e_dlog : e a₁ a₂ = gtGen ^ ((g1_dlog a₁) * (g2_dlog a₂))

axiom e_nondegen : e a₁ a₂ = gtOne ↔ (a₁ = zeroG1 ∨ a₂ = zeroG2)

/- The Plutus pairing bridge.
  `pi` = final exponentiation : MlResult → GT, a group homomorphism.
  `millerLoop` is NOT bilinear on the nose — only after `pi` (i.e. under
  `finalVerify`). NEVER state bilinearity as a raw MlResult equality.
  `mulMlResult` IS exact Fq12 multiplication, so assoc/comm hold on the nose. -/

axiom pi : BLS12_381_MlResult → GT

instance : Mul BLS12_381_MlResult := ⟨λ x y => (. * .) <$> x <*> y⟩

axiom mulMlResult_assoc : (m₁ * m₂) * m₃ = m₁ * (m₂ * m₃)
axiom mulMlResult_comm  : m₁ * m₂ = m₂ * m₁

axiom pi_millerLoop   : pi (bls12_381_millerLoop a₁ a₂) = e a₁ a₂
axiom pi_mulMlResult  : pi (m₁ * m₂) = (pi m₁) * (pi m₂)
axiom finalVerify_iff : bls12_381_finalVerify m₁ m₂ = true ↔ pi m₁ = pi m₂

/- Serialization.
   `uncompress : ByteString → Except String Gᵢ` is a partial injection onto the
   prime-order subgroup, right-inverse to `compress`. -/

axiom g1_uncompress_compress : bls12_381_G1_uncompress (bls12_381_G1_compress a₁) = Except.ok a₁
axiom g1_compress_uncompress : bls12_381_G1_uncompress b = Except.ok a₁ → bls12_381_G1_compress a₁ = b
axiom g1_uncompress_subgroup : bls12_381_G1_uncompress b = Except.ok a₁ → ∃ n : Int, a₁ = n * g1

axiom g2_uncompress_compress : bls12_381_G2_uncompress (bls12_381_G2_compress a₂) = Except.ok a₂
axiom g2_compress_uncompress : bls12_381_G2_uncompress b = Except.ok a₂ → bls12_381_G2_compress a₂ = b
axiom g2_uncompress_subgroup : bls12_381_G2_uncompress b = Except.ok a₂ → ∃ n : Int, a₂ = n * g2

/- Usable corollaries actually consumed by the verifier. -/

theorem finalVerify_millerLoop_pair :
  bls12_381_finalVerify (bls12_381_millerLoop a₁ a₂) (bls12_381_millerLoop b₁ b₂) = true ↔ e a₁ a₂ = e b₁ b₂ := by
    rw [finalVerify_iff, pi_millerLoop, pi_millerLoop]

theorem millerLoop_add_left_upto_finalVerify :
    bls12_381_finalVerify
      (bls12_381_millerLoop (a₁ + b₁) a₂)
      ((bls12_381_millerLoop a₁ a₂) * (bls12_381_millerLoop b₁ a₂)) = true := by
        rw [finalVerify_iff, pi_mulMlResult, pi_millerLoop, pi_millerLoop, pi_millerLoop, e_add_left]

end Internal

export Internal
  ( -- group axioms
    g1_add_assoc
    g1_add_comm
    g1_add_zero
    g1_add_neg
    g2_add_assoc
    g2_add_comm
    g2_add_zero
    g2_add_neg
    -- cyclic order
    g1_dlog
    g1_cyclic
    g1_dlog_scalarMul
    g1_order
    g2_dlog
    g2_cyclic
    g2_dlog_scalarMul
    g2_order
    -- scalar-action
    g1_scalarMul_zero
    g1_scalarMul_one
    g1_scalarMul_add_scalar
    g1_scalarMul_add_point
    g1_scalarMul_mul
    g1_scalarMul_mod
    g1_scalarMul_neg
    g2_scalarMul_zero
    g2_scalarMul_one
    g2_scalarMul_add_scalar
    g2_scalarMul_add_point
    g2_scalarMul_mul
    g2_scalarMul_mod
    g2_scalarMul_neg
    -- pairing
    GT
    gtOne
    gtMul
    gtGen
    gtPow
    e
    e_add_left
    e_add_right
    e_dlog
    e_nondegen
    -- pairing bridge
    pi
    mulMlResult_assoc
    mulMlResult_comm
    pi_millerLoop
    pi_mulMlResult
    finalVerify_iff
    -- serialization
    g1_uncompress_compress
    g1_compress_uncompress
    g1_uncompress_subgroup
    g2_uncompress_compress
    g2_compress_uncompress
    g2_uncompress_subgroup
    -- corollaries
    finalVerify_millerLoop_pair
    millerLoop_add_left_upto_finalVerify
  )

namespace PlutusCore.Crypto.BLS12_381.Axioms
