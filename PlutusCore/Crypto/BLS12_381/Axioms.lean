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

/- THE DOMAIN OF THESE AXIOMS: the order-r subgroup in most cases. -/

def InG1 (a : BLS12_381_G1_Element) : Prop := ∃ n : Int, a = n * g1
def InG2 (a : BLS12_381_G2_Element) : Prop := ∃ n : Int, a = n * g2

/- Scalar action at 0, 1 and -1. -/

axiom g1_scalarMul_zero : ( 0 : Int) * a₁ =   0
axiom g1_scalarMul_one  : ( 1 : Int) * a₁ =  a₁
axiom g1_scalarMul_neg  : (-1 : Int) * a₁ = -a₁

axiom g2_scalarMul_zero : ( 0 : Int) * a₂ =   0
axiom g2_scalarMul_one  : ( 1 : Int) * a₂ =  a₂
axiom g2_scalarMul_neg  : (-1 : Int) * a₂ = -a₂

theorem InG1_gen : InG1 g1 := ⟨1, (g1_scalarMul_one g1).symm⟩
theorem InG2_gen : InG2 g2 := ⟨1, (g2_scalarMul_one g2).symm⟩

theorem InG1_smul_gen : InG1 (n * g1) := ⟨n, rfl⟩
theorem InG2_smul_gen : InG2 (n * g2) := ⟨n, rfl⟩

theorem InG1_zero : InG1 0 := ⟨0, (g1_scalarMul_zero g1).symm⟩
theorem InG2_zero : InG2 0 := ⟨0, (g2_scalarMul_zero g2).symm⟩

/- Group axioms.
   (G1,+,0,neg) and (G2,+,0,neg) are abelian groups ON THE SUBGROUP.
   `add_zero` and `add_comm` need no restriction: `pointAdd` matches `infinity`
   structurally and is symmetric in its two arguments. -/

axiom g1_add_zero  : a₁ + 0 = a₁
axiom g1_add_comm  : a₁ + b₁ = b₁ + a₁
axiom g1_add_neg   : InG1 a₁ → a₁ + (-a₁) = 0
axiom g1_add_assoc :
  InG1 a₁ → InG1 b₁ → InG1 c₁
  -----------------------------
  → (a₁ + b₁) + c₁ = a₁ + (b₁ + c₁)

axiom g2_add_zero  : a₂ + 0 = a₂
axiom g2_add_comm  : a₂ + b₂ = b₂ + a₂
axiom g2_add_neg   : InG2 a₂ → a₂ + (-a₂) = 0
axiom g2_add_assoc :
  InG2 a₂ → InG2 b₂ → InG2 c₂
  -----------------------------
  → (a₂ + b₂) + c₂ = a₂ + (b₂ + c₂)

/- Scalar-action laws (ℤ/r-module), on the subgroup. -/

axiom g1_scalarMul_add_scalar : InG1 a₁            → (m + n) * a₁ = (m * a₁) + (n * a₁)
axiom g1_scalarMul_add_point  : InG1 a₁ → InG1 b₁ → n * (a₁ + b₁) = (n * a₁) + (n * b₁)
axiom g1_scalarMul_mul        : InG1 a₁            → (m * n) * a₁ = m * (n * a₁)
axiom g1_scalarMul_mod        : InG1 a₁            → (n % r) * a₁ = n * a₁

axiom g2_scalarMul_add_scalar : InG2 a₂            → (m + n) * a₂ = (m * a₂) + (n * a₂)
axiom g2_scalarMul_add_point  : InG2 a₂ → InG2 b₂ → n * (a₂ + b₂) = (n * a₂) + (n * b₂)
axiom g2_scalarMul_mul        : InG2 a₂            → (m * n) * a₂ = m * (n * a₂)
axiom g2_scalarMul_mod        : InG2 a₂            → (n % r) * a₂ = n * a₂

/- The subgroups are closed under the plus, scalar mul and mul opetations. -/

theorem InG1_add :
  InG1 a₁ → InG1 b₁ → InG1 (a₁ + b₁) :=
    by
      rintro ⟨i, rfl⟩ ⟨j, rfl⟩
      exact ⟨i + j, (g1_scalarMul_add_scalar g1 i j InG1_gen).symm⟩

theorem InG1_smul :
  InG1 a₁ → InG1 (n * a₁) :=
    by
      rintro ⟨i, rfl⟩
      exact ⟨n * i, (g1_scalarMul_mul g1 n i InG1_gen).symm⟩

theorem InG1_neg :
  InG1 a₁ → InG1 (-a₁) :=
    by
      intro h
      exact (g1_scalarMul_neg a₁ ▸ InG1_smul a₁ (-1) h)

theorem InG2_add :
  InG2 a₂ → InG2 b₂ → InG2 (a₂ + b₂) :=
    by
      rintro ⟨i, rfl⟩ ⟨j, rfl⟩
      exact ⟨i + j, (g2_scalarMul_add_scalar g2 i j InG2_gen).symm⟩

theorem InG2_smul :
  InG2 a₂ → InG2 (n * a₂) :=
    by
      rintro ⟨i, rfl⟩
      exact ⟨n * i, (g2_scalarMul_mul g2 n i InG2_gen).symm⟩

theorem InG2_neg :
  InG2 a₂ → InG2 (-a₂) :=
    by
      intro h
      exact (g2_scalarMul_neg a₂ ▸ InG2_smul a₂ (-1) h)

/- Prime cyclic order r.
   Each Gᵢ ≅ ℤ/r via a fixed generator. This is what collapses all group
   reasoning to modular arithmetic. `g1_dlog`/`g2_dlog` are the discrete logs
   into [0, r). `dlog_scalarMul` needs no restriction: it mentions no point
   other than the generator. -/

axiom g1_dlog : BLS12_381_G1_Element → Int
axiom g2_dlog : BLS12_381_G2_Element → Int

axiom g1_dlog_scalarMul : g1_dlog (n * g1) = n % r
axiom g2_dlog_scalarMul : g2_dlog (n * g2) = n % r

/- On the subgroup, `dlog` really is the discrete log. -/

theorem g1_cyclic :
  InG1 a₁ → a₁ = (g1_dlog a₁) * g1 :=
    by
      rintro ⟨i, rfl⟩
      rw [g1_dlog_scalarMul, g1_scalarMul_mod g1 i InG1_gen]

theorem g2_cyclic :
  InG2 a₂ → a₂ = (g2_dlog a₂) * g2 :=
    by
      rintro ⟨i, rfl⟩
      rw [g2_dlog_scalarMul, g2_scalarMul_mod g2 i InG2_gen]

/- The generator's order DIVIDES r (checked on the concrete curve). -/

theorem g1_order : r * g1 = 0 := by decide +native
theorem g2_order : r * g2 = 0 := by decide +native

/- Bilinear pairing.
   Modeled through an abstract target group `GT` (order r) and the abstract pairing `e : G1 → G2 → GT`. -/

/- Abstract pairing target `G_T`: an opaque type with opaque `1`, `*`, `^` and a
   distinguished `gtGen`. Deliberately NO group law is assumed for `gtMul`; the
   only structural fact is `gtPow_inj_mod` below, and every product that arises
   is collapsed through `gtPow_add`. -/
axiom GT : Type
axiom gtOne : GT
axiom gtMul : GT → GT → GT
axiom gtGen : GT  -- distinguished element; note `e g1 g2 = gtGen ^ (1 : Int)`
axiom gtPow : GT → Int → GT

noncomputable instance : One GT := ⟨gtOne⟩
noncomputable instance : Mul GT := ⟨gtMul⟩
noncomputable instance : HPow GT Int GT := ⟨gtPow⟩

/- The pairing itself. -/
axiom e : BLS12_381_G1_Element → BLS12_381_G2_Element → GT

axiom e_add_left  : InG1 a₁ → InG1 b₁ → InG2 a₂ → e (a₁ + b₁) a₂ = (e a₁ a₂) * (e b₁ a₂)
axiom e_add_right : InG1 a₁ → InG2 a₂ → InG2 b₂ → e a₁ (a₂ + b₂) = (e a₁ a₂) * (e a₁ b₂)

axiom e_dlog     : InG1 a₁ → InG2 a₂ → e a₁ a₂ = gtGen ^ ((g1_dlog a₁) * (g2_dlog a₂))
axiom e_nondegen : InG1 a₁ → InG2 a₂ → (e a₁ a₂ = gtOne ↔ (a₁ = zeroG1 ∨ a₂ = zeroG2))

axiom gtPow_inj_mod : gtGen ^ m = gtGen ^ n ↔ m % r = n % r

/- The Plutus pairing bridge.
  `pi` = final exponentiation : MlResult → GT, a group homomorphism.
  `millerLoop` is NOT bilinear on the nose -- only after `pi` (i.e. under `finalVerify`).
  NEVER state bilinearity as a raw MlResult equality.
  `mulMlResult` IS exact Fq12 multiplication, so assoc/comm hold on the nose. -/

axiom pi : BLS12_381_MlResult → GT

instance : Mul BLS12_381_MlResult := ⟨bls12_381_mulMlResult⟩

axiom mulMlResult_assoc : (m₁ * m₂) * m₃ = m₁ * (m₂ * m₃)
axiom mulMlResult_comm  : m₁ * m₂ = m₂ * m₁

/- THE SECOND DOMAIN RESTRICTION: not every `BLS12_381_MlResult` is a Miller-loop value.
   The type is `Option Fq12`, and `calculateMillerLoop` returns `none` at the identity,
   which `mulMlResult` absorbs (`none * m = none`) and `finalVerify` reports as a hard `false`.
   `MlOk` marks the values on which `pi` is a homomorphism: `some x` with `x` a unit of Fq12. -/
axiom MlOk : BLS12_381_MlResult → Prop

axiom millerLoop_ok      : InG1 a₁ → a₁ ≠ 0 → InG2 a₂ → a₂ ≠ 0 → MlOk (bls12_381_millerLoop a₁ a₂)
axiom mulMlResult_ok     : MlOk m₁ → MlOk m₂ → MlOk (m₁ * m₂)
axiom mulMlResult_ok_inv : MlOk (m₁ * m₂) → MlOk m₁ ∧ MlOk m₂

axiom pi_millerLoop  : pi (bls12_381_millerLoop a₁ a₂) = e a₁ a₂
axiom pi_mulMlResult : MlOk m₁ → MlOk m₂ → pi (m₁ * m₂) = (pi m₁) * (pi m₂)

axiom finalVerify_sound    : bls12_381_finalVerify m₁ m₂ = true → pi m₁ = pi m₂
axiom finalVerify_ok       : bls12_381_finalVerify m₁ m₂ = true → MlOk m₁ ∧ MlOk m₂
axiom finalVerify_complete : MlOk m₁ → MlOk m₂ → pi m₁ = pi m₂ → bls12_381_finalVerify m₁ m₂ = true

/- Serialization. -/

axiom g1_uncompress_compress : InG1 a₁ → bls12_381_G1_uncompress (bls12_381_G1_compress a₁) = Except.ok a₁
axiom g1_compress_uncompress : bls12_381_G1_uncompress b = Except.ok a₁ → bls12_381_G1_compress a₁ = b
axiom g1_uncompress_subgroup : bls12_381_G1_uncompress b = Except.ok a₁ → InG1 a₁

axiom g2_uncompress_compress : InG2 a₂ → bls12_381_G2_uncompress (bls12_381_G2_compress a₂) = Except.ok a₂
axiom g2_compress_uncompress : bls12_381_G2_uncompress b = Except.ok a₂ → bls12_381_G2_compress a₂ = b
axiom g2_uncompress_subgroup : bls12_381_G2_uncompress b = Except.ok a₂ → InG2 a₂

/- Useful corollaries. -/

/- Soundness of the two-Miller-loop check: unconditional. -/
theorem finalVerify_millerLoop_pair_sound :
    bls12_381_finalVerify (bls12_381_millerLoop a₁ a₂) (bls12_381_millerLoop b₁ b₂) = true →
    -----------------------------------------------------------------------------------------
    e a₁ a₂ = e b₁ b₂ :=
      by
        intro h
        have hfs := finalVerify_sound _ _ h
        rwa [pi_millerLoop, pi_millerLoop] at hfs

/- The converse needs both Miller loops to be genuine -- i.e. nonzero subgroup arguments, which is what `millerLoop_ok` turns into `MlOk`. -/
theorem finalVerify_millerLoop_pair :
  InG1 a₁ → a₁ ≠ 0 → InG2 a₂ → a₂ ≠ 0 → InG1 b₁ → b₁ ≠ 0 → InG2 b₂ → b₂ ≠ 0 →
  -----------------------------------------------------------------------------------
  (bls12_381_finalVerify (bls12_381_millerLoop a₁ a₂) (bls12_381_millerLoop b₁ b₂) = true ↔ e a₁ a₂ = e b₁ b₂) :=
    by
      intro ha ha0 hb hb0 hc hc0 hd hd0
      refine ⟨finalVerify_millerLoop_pair_sound _ _ _ _, fun h => ?_⟩
      refine finalVerify_complete _ _ (millerLoop_ok a₁ a₂ ha ha0 hb hb0)
        (millerLoop_ok b₁ b₂ hc hc0 hd hd0) ?_
      rwa [pi_millerLoop, pi_millerLoop]

theorem millerLoop_add_left_upto_finalVerify :
  InG1 a₁ → a₁ ≠ 0 → InG1 b₁ → b₁ ≠ 0 → InG2 a₂ → a₂ ≠ 0 → a₁ + b₁ ≠ 0 →
  -----------------------------------------------------------------------------
  bls12_381_finalVerify
    (bls12_381_millerLoop (a₁ + b₁) a₂)
    ((bls12_381_millerLoop a₁ a₂) * (bls12_381_millerLoop b₁ a₂)) = true :=
      by
        intro ha ha0 hb hb0 hc hc0 hab0
        refine finalVerify_complete _ _
          (millerLoop_ok _ _ (InG1_add a₁ b₁ ha hb) hab0 hc hc0)
          (mulMlResult_ok _ _ (millerLoop_ok _ _ ha ha0 hc hc0)
                              (millerLoop_ok _ _ hb hb0 hc hc0)) ?_
        rw [pi_mulMlResult _ _ (millerLoop_ok _ _ ha ha0 hc hc0)
              (millerLoop_ok _ _ hb hb0 hc hc0),
            pi_millerLoop, pi_millerLoop, pi_millerLoop, e_add_left a₁ b₁ a₂ ha hb hc]

/- Modular arithmetic in ℤ/r. -/

theorem emod_eq_of_sub_eq {k x y u v : Int} (h : u % k = v % k) (huv : u - v = x - y) :
  x % k = y % k :=
    by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h ⊢
      rwa [←huv]

theorem g1_zero_add : 0 + a₁ = a₁ := by rw [g1_add_comm]; exact g1_add_zero a₁
theorem g2_zero_add : 0 + a₂ = a₂ := by rw [g2_add_comm]; exact g2_add_zero a₂

theorem g1_add_right_cancel :
  InG1 a₁ → InG1 b₁ → InG1 c₁ → a₁ + c₁ = b₁ + c₁
  --------------------------------------------------
  → a₁ = b₁ :=
    by
      intro ha hb hc h
      calc a₁ = a₁ + 0          := (g1_add_zero a₁).symm
           _  = a₁ + (c₁ + -c₁) := by rw [g1_add_neg c₁ hc]
           _  = (a₁ + c₁) + -c₁ := (g1_add_assoc a₁ c₁ (-c₁) ha hc (InG1_neg c₁ hc)).symm
           _  = (b₁ + c₁) + -c₁ := by rw [h]
           _  = b₁ + (c₁ + -c₁) := g1_add_assoc b₁ c₁ (-c₁) hb hc (InG1_neg c₁ hc)
           _  = b₁ + 0          := by rw [g1_add_neg c₁ hc]
           _  = b₁              := g1_add_zero b₁

theorem g2_add_right_cancel :
  InG2 a₂ → InG2 b₂ → InG2 c₂ → a₂ + c₂ = b₂ + c₂
  --------------------------------------------------
  → a₂ = b₂ :=
    by
      intro ha hb hc h
      calc a₂ = a₂ + 0          := (g2_add_zero a₂).symm
           _  = a₂ + (c₂ + -c₂) := by rw [g2_add_neg c₂ hc]
           _  = (a₂ + c₂) + -c₂ := (g2_add_assoc a₂ c₂ (-c₂) ha hc (InG2_neg c₂ hc)).symm
           _  = (b₂ + c₂) + -c₂ := by rw [h]
           _  = b₂ + (c₂ + -c₂) := g2_add_assoc b₂ c₂ (-c₂) hb hc (InG2_neg c₂ hc)
           _  = b₂ + 0          := by rw [g2_add_neg c₂ hc]
           _  = b₂              := g2_add_zero b₂

theorem g1_dlog_zero : g1_dlog 0 = 0 :=
  by
    conv => lhs; rw [←g1_scalarMul_zero g1, g1_dlog_scalarMul]
    exact Int.zero_emod r

theorem g2_dlog_zero : g2_dlog 0 = 0 :=
  by
    conv => lhs; rw [←g2_scalarMul_zero g2, g2_dlog_scalarMul]
    exact Int.zero_emod r

theorem g1_dlog_add :
  InG1 a₁ → InG1 b₁
  ------------------
  → g1_dlog (a₁ + b₁) = (g1_dlog a₁ + g1_dlog b₁) % r :=
    by
      intro ha hb
      conv => lhs; rw [g1_cyclic a₁ ha, g1_cyclic b₁ hb, ←g1_scalarMul_add_scalar _ _ _ InG1_gen, g1_dlog_scalarMul]

theorem g2_dlog_add :
  InG2 a₂ → InG2 b₂
  ------------------
  → g2_dlog (a₂ + b₂) = (g2_dlog a₂ + g2_dlog b₂) % r :=
    by
      intro ha hb
      conv => lhs; rw [g2_cyclic a₂ ha, g2_cyclic b₂ hb, ←g2_scalarMul_add_scalar _ _ _ InG2_gen, g2_dlog_scalarMul]

theorem g1_dlog_scalarMul_point :
  InG1 a₁ → g1_dlog (n * a₁) = (n * g1_dlog a₁) % r :=
    by
      intro ha
      conv => lhs; rw [g1_cyclic a₁ ha, ← g1_scalarMul_mul _ _ _ InG1_gen, g1_dlog_scalarMul]

theorem g2_dlog_scalarMul_point :
  InG2 a₂ → g2_dlog (n * a₂) = (n * g2_dlog a₂) % r :=
    by
      intro ha
      conv => lhs; rw [g2_cyclic a₂ ha, ← g2_scalarMul_mul _ _ _ InG2_gen, g2_dlog_scalarMul]

theorem g1_dlog_emod_eq_zero_iff :
  InG1 a₁ → (g1_dlog a₁ % r = 0 ↔ a₁ = 0) :=
    by
      intro ha
      constructor <;> intro h
      · have h₀ : a₁ = (g1_dlog a₁ % r) * g1 := by rw [g1_scalarMul_mod g1 _ InG1_gen]; exact g1_cyclic a₁ ha
        rw [h₀, h, g1_scalarMul_zero]
      · rw [h, g1_dlog_zero]
        exact Int.zero_emod r

theorem g2_dlog_emod_eq_zero_iff :
  InG2 a₂ → (g2_dlog a₂ % r = 0 ↔ a₂ = 0) :=
    by
      intro ha
      constructor <;> intro h
      · have h₀ : a₂ = (g2_dlog a₂ % r) * g2 := by rw [g2_scalarMul_mod g2 _ InG2_gen]; exact g2_cyclic a₂ ha
        rw [h₀, h, g2_scalarMul_zero]
      · rw [h, g2_dlog_zero]
        exact Int.zero_emod r

theorem g1_dlog_gen :
  g1_dlog g1 = 1 :=
    by
      conv => lhs; rw [←g1_scalarMul_one g1, g1_dlog_scalarMul]
      decide

theorem g2_dlog_gen :
  g2_dlog g2 = 1 :=
    by
      conv => lhs; rw [←g2_scalarMul_one g2, g2_dlog_scalarMul]
      decide

theorem g1_emod_eq_zero_of_smul_gen :
  ∀ (n : Int), n * g1 = 0 → n % r = 0 :=
    by
      intro n h
      rw [← g1_dlog_scalarMul n, h]
      exact g1_dlog_zero

theorem g2_emod_eq_zero_of_smul_gen :
  ∀ (n : Int), n * g2 = 0 → n % r = 0 :=
    by
      intro n h
      rw [← g2_dlog_scalarMul n, h]
      exact g2_dlog_zero

theorem e_eq_iff_dlog :
  InG1 a₁ → InG2 a₂ → InG1 b₁ → InG2 b₂
  ----------------------------------------
  → (e a₁ a₂ = e b₁ b₂ ↔ (g1_dlog a₁ * g2_dlog a₂) % r = (g1_dlog b₁ * g2_dlog b₂) % r) :=
    by
      intro ha ha' hb hb'
      rw [e_dlog a₁ a₂ ha ha', e_dlog b₁ b₂ hb hb', gtPow_inj_mod]

theorem gtOne_eq_gtPow_zero :
  gtOne = gtGen ^ (0 : Int) :=
    by
      have h1 : e 0 0 = gtOne                           := (e_nondegen 0 0 InG1_zero InG2_zero).mpr (Or.inl rfl)
      have h2 : e 0 0 = gtGen ^ (g1_dlog 0 * g2_dlog 0) := e_dlog 0 0 InG1_zero InG2_zero
      rw [g1_dlog_zero, Int.zero_mul] at h2
      rw [←h1, h2]

theorem gtPow_emod (k : Int) :
  gtGen ^ (k % r) = gtGen ^ k := (gtPow_inj_mod _ _).mpr (Int.emod_emod k r)

theorem gtPow_add :
  gtGen ^ (m + n) = gtGen ^ m * gtGen ^ n :=
    by
      have h := e_add_left (m * g1) (n * g1) g2 (InG1_smul_gen m) (InG1_smul_gen n) InG2_gen
      rw [←g1_scalarMul_add_scalar _ _ _ InG1_gen] at h
      rw [e_dlog _ _ (InG1_smul_gen (m + n)) InG2_gen, e_dlog _ _ (InG1_smul_gen m) InG2_gen, e_dlog _ _ (InG1_smul_gen n) InG2_gen] at h
      simp only [g1_dlog_scalarMul, g2_dlog_gen, Int.mul_one] at h
      rw [gtPow_emod, gtPow_emod, gtPow_emod] at h
      exact h

theorem groupOrder_prime :
  (m * n) % r = 0
  ---------------
  → m % r = 0 ∨ n % r = 0 :=
    by
      intro h
      have hE : e (m * g1) (n * g2) = gtOne := by
        rw [e_dlog _ _ (InG1_smul_gen m) (InG2_smul_gen n), g1_dlog_scalarMul, g2_dlog_scalarMul, gtOne_eq_gtPow_zero]
        exact (gtPow_inj_mod _ _).mpr (by rw [← Int.mul_emod, h, Int.zero_emod])
      have hnE : m * g1 = 0 ∨ n * g2 = 0 := (e_nondegen _ _ (InG1_smul_gen m) (InG2_smul_gen n)).mp hE
      match hnE with
      | .inl hl => exact (.inl (g1_emod_eq_zero_of_smul_gen m hl))
      | .inr hr => exact (.inr (g2_emod_eq_zero_of_smul_gen n hr))

theorem emod_cancel_mul_right :
  ∀ (x y d : Int), d % r ≠ 0 → (x * d) % r = (y * d) % r
  -------------------------------------------------------
  → x % r = y % r :=
    by
      intro x y d hd h
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h ⊢
      rw [←Int.sub_mul] at h
      exact (groupOrder_prime _ _ h).resolve_right hd

theorem emod_cancel_mul_left :
  ∀ (x y d : Int), d % r ≠ 0 → (d * x) % r = (d * y) % r
  -------------------------------------------------------
  → x % r = y % r :=
    by
      intro x y d hd h
      rw [Int.mul_comm d x, Int.mul_comm d y] at h
      exact emod_cancel_mul_right x y d hd h

end Internal

export Internal
  ( -- constants
    r
    zeroG1
    zeroG2
    -- the order-r subgroup: the domain of every axiom below
    InG1
    InG2
    InG1_gen
    InG2_gen
    InG1_smul_gen
    InG2_smul_gen
    InG1_zero
    InG2_zero
    InG1_add
    InG2_add
    InG1_smul
    InG2_smul
    InG1_neg
    InG2_neg
    -- group axioms
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
    gtPow_inj_mod
    -- pairing bridge
    pi
    mulMlResult_assoc
    mulMlResult_comm
    MlOk
    millerLoop_ok
    mulMlResult_ok
    mulMlResult_ok_inv
    pi_millerLoop
    pi_mulMlResult
    finalVerify_sound
    finalVerify_ok
    finalVerify_complete
    -- serialization
    g1_uncompress_compress
    g1_compress_uncompress
    g1_uncompress_subgroup
    g2_uncompress_compress
    g2_compress_uncompress
    g2_uncompress_subgroup
    -- corollaries
    finalVerify_millerLoop_pair_sound
    finalVerify_millerLoop_pair
    millerLoop_add_left_upto_finalVerify
    -- modular arithmetic in ℤ/r
    emod_eq_of_sub_eq
    -- group cancellation
    g1_zero_add
    g2_zero_add
    g1_add_right_cancel
    g2_add_right_cancel
    -- dlog is an isomorphism onto ℤ/r
    g1_dlog_zero
    g2_dlog_zero
    g1_dlog_add
    g2_dlog_add
    g1_dlog_scalarMul_point
    g2_dlog_scalarMul_point
    g1_dlog_emod_eq_zero_iff
    g2_dlog_emod_eq_zero_iff
    g1_dlog_gen
    g2_dlog_gen
    -- generator order exactly r (converse of g1_order / g2_order)
    g1_emod_eq_zero_of_smul_gen
    g2_emod_eq_zero_of_smul_gen
    -- G_T of order exactly r: no zero divisors mod r, and the consequences consumed
    e_eq_iff_dlog
    gtOne_eq_gtPow_zero
    gtPow_emod
    gtPow_add
    groupOrder_prime
    emod_cancel_mul_right
    emod_cancel_mul_left
  )

end PlutusCore.Crypto.BLS12_381.Axioms
