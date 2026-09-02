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

/- THE DOMAIN OF THESE AXIOMS: the order-r subgroup in most cases.

   `opaque` rather than `def`, with `InG1_def` as the only way in or out. The definition is
   the intended one and is right there in the body; what `opaque` buys is that it does not
   *unfold*, and every consumer of this file wants that:

   * Blaster translates an `opaque` as a `declare-fun`, i.e. the uninterpreted predicate a
     guarded axiom actually wants. As a `def` it unfolded into `n * g1`, whose `Cryptograph`
     scalar action bottoms out in the `partial def` `binaryInversion.loop`, and
     `normConst` refuses those -- which put every `InG1`/`InG2`-guarded axiom out of
     `blaster`'s reach whatever the route. With the guard opaque, `PairingAlg` and
     `SerdeAlg` translate; see `BlasterAlg` at the end of this file.
   * The kernel-side proofs never needed the definition, only the closure lemmas below, and
     those are re-proved through `InG1_def` at no cost.

   The trade is one axiom per group. `InG1_def` is not provable -- that is what `opaque`
   means -- but it is definitional rather than an assumption about the curve: the body is
   the witness that a model exists. Do not restate it in a module that runs `blaster`; a
   same-module Prop axiom is harvested into *every* query there (see
   `Tests/AxiomsBlasterHarvest.lean`), and this one mentions `n * g1`, so it would hard-error
   goals that never mention `InG1` at all. -/

opaque InG1 (a : BLS12_381_G1_Element) : Prop := ∃ n : Int, a = n * g1
opaque InG2 (a : BLS12_381_G2_Element) : Prop := ∃ n : Int, a = n * g2

axiom InG1_def : InG1 a₁ ↔ ∃ n : Int, a₁ = n * g1
axiom InG2_def : InG2 a₂ ↔ ∃ n : Int, a₂ = n * g2

/- Scalar action at 0, 1 and -1. -/

axiom g1_scalarMul_zero : ( 0 : Int) * a₁ =   0
axiom g1_scalarMul_one  : ( 1 : Int) * a₁ =  a₁
axiom g1_scalarMul_neg  : (-1 : Int) * a₁ = -a₁

axiom g2_scalarMul_zero : ( 0 : Int) * a₂ =   0
axiom g2_scalarMul_one  : ( 1 : Int) * a₂ =  a₂
axiom g2_scalarMul_neg  : (-1 : Int) * a₂ = -a₂

theorem InG1_gen : InG1 g1 := (InG1_def g1).mpr ⟨1, (g1_scalarMul_one g1).symm⟩
theorem InG2_gen : InG2 g2 := (InG2_def g2).mpr ⟨1, (g2_scalarMul_one g2).symm⟩

theorem InG1_smul_gen : InG1 (n * g1) := (InG1_def _).mpr ⟨n, rfl⟩
theorem InG2_smul_gen : InG2 (n * g2) := (InG2_def _).mpr ⟨n, rfl⟩

theorem InG1_zero : InG1 0 := (InG1_def 0).mpr ⟨0, (g1_scalarMul_zero g1).symm⟩
theorem InG2_zero : InG2 0 := (InG2_def 0).mpr ⟨0, (g2_scalarMul_zero g2).symm⟩

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
      intro ha hb
      obtain ⟨i, rfl⟩ := (InG1_def a₁).mp ha
      obtain ⟨j, rfl⟩ := (InG1_def b₁).mp hb
      exact (InG1_def _).mpr ⟨i + j, (g1_scalarMul_add_scalar g1 i j InG1_gen).symm⟩

theorem InG1_smul :
  InG1 a₁ → InG1 (n * a₁) :=
    by
      intro ha
      obtain ⟨i, rfl⟩ := (InG1_def a₁).mp ha
      exact (InG1_def _).mpr ⟨n * i, (g1_scalarMul_mul g1 n i InG1_gen).symm⟩

theorem InG1_neg :
  InG1 a₁ → InG1 (-a₁) :=
    by
      intro h
      exact (g1_scalarMul_neg a₁ ▸ InG1_smul a₁ (-1) h)

theorem InG2_add :
  InG2 a₂ → InG2 b₂ → InG2 (a₂ + b₂) :=
    by
      intro ha hb
      obtain ⟨i, rfl⟩ := (InG2_def a₂).mp ha
      obtain ⟨j, rfl⟩ := (InG2_def b₂).mp hb
      exact (InG2_def _).mpr ⟨i + j, (g2_scalarMul_add_scalar g2 i j InG2_gen).symm⟩

theorem InG2_smul :
  InG2 a₂ → InG2 (n * a₂) :=
    by
      intro ha
      obtain ⟨i, rfl⟩ := (InG2_def a₂).mp ha
      exact (InG2_def _).mpr ⟨n * i, (g2_scalarMul_mul g2 n i InG2_gen).symm⟩

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
      intro ha
      obtain ⟨i, rfl⟩ := (InG1_def a₁).mp ha
      rw [g1_dlog_scalarMul, g1_scalarMul_mod g1 i InG1_gen]

theorem g2_cyclic :
  InG2 a₂ → a₂ = (g2_dlog a₂) * g2 :=
    by
      intro ha
      obtain ⟨i, rfl⟩ := (InG2_def a₂).mp ha
      rw [g2_dlog_scalarMul, g2_scalarMul_mod g2 i InG2_gen]

/- The generator's order DIVIDES r (checked on the concrete curve). -/

theorem g1_order : r * g1 = 0 := by decide +native
theorem g2_order : r * g2 = 0 := by decide +native

/- Bilinear pairing.
   Modeled through the target group `GT` (order r) and the abstract pairing `e : G1 → G2 → GT`. -/

/- Pairing target `G_T`, as ℤ/r.

   `G_T` is cyclic of order r and nothing below uses more than that, so it is *modelled*
   rather than assumed: an element is its discrete log to base `gtGen`, reduced into
   [0, r). This is the same collapse `g1_dlog`/`g2_dlog` perform for G1 and G2, and the
   reason it is worth doing here is that an `axiom GT : Type` is an uninterpreted sort,
   which Blaster cannot translate.

   `e` and `pi` stay uninterpreted. `e_dlog` pins `e` only on the order-r subgroup, and
   `pi_millerLoop` is unguarded, so *defining* `e` by the dlogs would fix its value where
   nothing licenses that.

   Every element must be built through `mkGT`, `gtOne`, `gtGen`, `gtMul` or `gtPow`, all
   of which reduce mod r. `GT.mk` admits unnormalized junk (`⟨-5⟩` denotes no group
   element); that is harmless only because no statement in this file quantifies over a
   bare `GT` variable, and it must stay that way. -/
structure GT where
  exp : Int

/-- The element `gtGen ^ n`. The only intended way to build a `GT`. -/
def mkGT (n : Int) : GT := ⟨n % r⟩

def gtOne : GT := ⟨0⟩
def gtGen : GT := ⟨1⟩  -- note `e g1 g2 = gtGen ^ (1 : Int)`
def gtMul (a b : GT) : GT := mkGT (a.exp + b.exp)
def gtPow (a : GT) (n : Int) : GT := mkGT (a.exp * n)

instance : One GT := ⟨gtOne⟩
instance : Mul GT := ⟨gtMul⟩
instance : HPow GT Int GT := ⟨gtPow⟩

/- The pairing itself. -/
axiom e : BLS12_381_G1_Element → BLS12_381_G2_Element → GT

/- Bilinearity is NOT assumed. Under the ℤ/r model `e_dlog` already determines `e` on the
   subgroup, so `e_add_left` and `e_add_right` are theorems -- proved at the end of this
   file, where `g1_dlog_add` and `gtPow_add` are available. -/

axiom e_dlog     : InG1 a₁ → InG2 a₂ → e a₁ a₂ = gtGen ^ ((g1_dlog a₁) * (g2_dlog a₂))
axiom e_nondegen : InG1 a₁ → InG2 a₂ → (e a₁ a₂ = gtOne ↔ (a₁ = zeroG1 ∨ a₂ = zeroG2))

/- `gtGen` has order exactly r. Was an axiom while `GT` was abstract; now it is what the
   ℤ/r model says, and the only structural fact about `G_T` that anything below uses. -/
theorem gtPow_inj_mod : gtGen ^ m = gtGen ^ n ↔ m % r = n % r :=
  by
    show gtPow gtGen m = gtPow gtGen n ↔ _
    simp only [gtPow, gtGen, mkGT, GT.mk.injEq, Int.one_mul]

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

/- These three are facts about ℤ/r and nothing else. Each used to be routed through the
   pairing -- `gtOne_eq_gtPow_zero` via `e_nondegen`, `gtPow_add` via `e_add_left` -- which
   made a pure arithmetic statement depend on ten curve axioms. Under the model they are
   arithmetic, and depend on nothing. -/

theorem gtOne_eq_gtPow_zero :
  gtOne = gtGen ^ (0 : Int) :=
    by
      show gtOne = gtPow gtGen 0
      simp only [gtOne, gtPow, gtGen, mkGT, Int.one_mul, Int.zero_emod]

theorem gtPow_emod (k : Int) :
  gtGen ^ (k % r) = gtGen ^ k := (gtPow_inj_mod _ _).mpr (Int.emod_emod k r)

theorem gtPow_add :
  gtGen ^ (m + n) = gtGen ^ m * gtGen ^ n :=
    by
      show gtPow gtGen (m + n) = gtMul (gtPow gtGen m) (gtPow gtGen n)
      simp only [gtPow, gtMul, gtGen, mkGT, GT.mk.injEq, Int.one_mul]
      rw [Int.add_emod (m % r) (n % r) r, Int.emod_emod, Int.emod_emod, ← Int.add_emod]

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

/- Bilinearity of the pairing, derived.

   `e_dlog` sends both sides into ℤ/r, `g1_dlog_add`/`g2_dlog_add` turn the point addition
   into addition of discrete logs, and `gtPow_add` turns the product in `G_T` back into
   addition of exponents; what is left is distributivity mod r. -/

theorem e_add_left :
  InG1 a₁ → InG1 b₁ → InG2 a₂
  -----------------------------
  → e (a₁ + b₁) a₂ = (e a₁ a₂) * (e b₁ a₂) :=
    by
      intro ha hb hc
      rw [e_dlog _ _ (InG1_add a₁ b₁ ha hb) hc, e_dlog _ _ ha hc, e_dlog _ _ hb hc,
          g1_dlog_add a₁ b₁ ha hb, ← gtPow_add, gtPow_inj_mod, Int.mul_emod,
          Int.emod_emod, ← Int.mul_emod, Int.add_mul]

theorem e_add_right :
  InG1 a₁ → InG2 a₂ → InG2 b₂
  -----------------------------
  → e a₁ (a₂ + b₂) = (e a₁ a₂) * (e a₁ b₂) :=
    by
      intro ha hb hc
      rw [e_dlog _ _ ha (InG2_add a₂ b₂ hb hc), e_dlog _ _ ha hb, e_dlog _ _ ha hc,
          g2_dlog_add a₂ b₂ hb hc, ← gtPow_add, gtPow_inj_mod, Int.mul_emod,
          Int.emod_emod, ← Int.mul_emod, Int.mul_add]

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

/- THE AXIOMS AS BUNDLES.

   Every Prop-typed axiom of this file, grouped by the sections above, as closed `Prop`s.
   `DlogFacts` is the one exception: derived facts rather than axioms, bundled for the same
   route-C reason but costing nothing in the trust base.

   Translatability: five of the seven reach the solver as they stand, and `BlasterAlg`
   collects them -- 18 of the 42. `G1Alg` and `G2Alg` need one extra step from the consumer,
   because their *conclusions* are equations in the `Cryptograph` `+`/`*`, computable
   operations that bottom out in the `partial def` `binaryInversion.loop`, which `normConst`
   refuses. Marking the four `Cryptograph` `Point` instances `irreducible` in the consuming
   module stops blaster descending that far and leaves the operations as uninterpreted
   functions, at which point both bundles translate -- no restatement here, and no axiom
   added. `Tests/AxiomsBlasterSealed.lean` measures it, and carries the vacuity guards that
   the trick needs. Two caveats live there too: state the two or three laws a goal needs
   rather than a whole bundle (twelve conjuncts at once leaves the solver `Undetermined`),
   and the seal must go in the consuming module, since it changes every `blaster` call after
   it. -/

/-- The G1 group: the scalar action at 0, 1 and -1, the abelian group laws, the ℤ/r-module laws
    on the subgroup, and the discrete log of a multiple of the generator.

    Usable by `blaster` only in a module that seals the `Cryptograph` `Point` instances, and
    then a slice at a time rather than whole -- see `Tests/AxiomsBlasterSealed.lean`. -/
def G1Alg : Prop :=
  (∀ (p : BLS12_381_G1_Element), ( 0 : Int) * p =  0) ∧
  (∀ (p : BLS12_381_G1_Element), ( 1 : Int) * p =  p) ∧
  (∀ (p : BLS12_381_G1_Element), (-1 : Int) * p = -p) ∧
  (∀ (p : BLS12_381_G1_Element), p + 0 = p) ∧
  (∀ (p q : BLS12_381_G1_Element), p + q = q + p) ∧
  (∀ (p : BLS12_381_G1_Element), InG1 p → p + -p = 0) ∧
  (∀ (p q s : BLS12_381_G1_Element),
     InG1 p → InG1 q → InG1 s → (p + q) + s = p + (q + s)) ∧
  (∀ (p : BLS12_381_G1_Element) (i j : Int), InG1 p → (i + j) * p = (i * p) + (j * p)) ∧
  (∀ (p q : BLS12_381_G1_Element) (i : Int),
     InG1 p → InG1 q → i * (p + q) = (i * p) + (i * q)) ∧
  (∀ (p : BLS12_381_G1_Element) (i j : Int), InG1 p → (i * j) * p = i * (j * p)) ∧
  (∀ (p : BLS12_381_G1_Element) (i : Int), InG1 p → (i % r) * p = i * p) ∧
  (∀ (i : Int), g1_dlog (i * g1) = i % r)

theorem g1Alg : G1Alg :=
  ⟨g1_scalarMul_zero, g1_scalarMul_one, g1_scalarMul_neg,
   g1_add_zero, g1_add_comm, g1_add_neg, g1_add_assoc,
   g1_scalarMul_add_scalar, g1_scalarMul_add_point, g1_scalarMul_mul, g1_scalarMul_mod,
   g1_dlog_scalarMul⟩

/-- `G1Alg` for G2, statement for statement. -/
def G2Alg : Prop :=
  (∀ (p : BLS12_381_G2_Element), ( 0 : Int) * p =  0) ∧
  (∀ (p : BLS12_381_G2_Element), ( 1 : Int) * p =  p) ∧
  (∀ (p : BLS12_381_G2_Element), (-1 : Int) * p = -p) ∧
  (∀ (p : BLS12_381_G2_Element), p + 0 = p) ∧
  (∀ (p q : BLS12_381_G2_Element), p + q = q + p) ∧
  (∀ (p : BLS12_381_G2_Element), InG2 p → p + -p = 0) ∧
  (∀ (p q s : BLS12_381_G2_Element),
     InG2 p → InG2 q → InG2 s → (p + q) + s = p + (q + s)) ∧
  (∀ (p : BLS12_381_G2_Element) (i j : Int), InG2 p → (i + j) * p = (i * p) + (j * p)) ∧
  (∀ (p q : BLS12_381_G2_Element) (i : Int),
     InG2 p → InG2 q → i * (p + q) = (i * p) + (i * q)) ∧
  (∀ (p : BLS12_381_G2_Element) (i j : Int), InG2 p → (i * j) * p = i * (j * p)) ∧
  (∀ (p : BLS12_381_G2_Element) (i : Int), InG2 p → (i % r) * p = i * p) ∧
  (∀ (i : Int), g2_dlog (i * g2) = i % r)

theorem g2Alg : G2Alg :=
  ⟨g2_scalarMul_zero, g2_scalarMul_one, g2_scalarMul_neg,
   g2_add_zero, g2_add_comm, g2_add_neg, g2_add_assoc,
   g2_scalarMul_add_scalar, g2_scalarMul_add_point, g2_scalarMul_mul, g2_scalarMul_mod,
   g2_dlog_scalarMul⟩

/-- Commutativity and associativity of `mulMlResult`, which are exact -- `mulMlResult` is
    Fq12 multiplication, with no domain restriction. Harvestable in one line by a
    `blaster`-facing module: see `Tests/AxiomsBlasterHarvest.lean`. -/
def MlAlg : Prop :=
  (∀ (x y   : BLS12_381_MlResult), x * y = y * x) ∧
  (∀ (x y z : BLS12_381_MlResult), (x * y) * z = x * (y * z))

theorem mlAlg : MlAlg := ⟨mulMlResult_comm, mulMlResult_assoc⟩

/-- `MlOk` is closed under products, and only products of `MlOk` values are `MlOk`.
    Translatable: `MlOk` is an `axiom _ : _ → Prop`, hence an uninterpreted predicate. -/
def MlOkAlg : Prop :=
  (∀ (x y : BLS12_381_MlResult), MlOk x → MlOk y → MlOk (x * y)) ∧
  (∀ (x y : BLS12_381_MlResult), MlOk (x * y) → MlOk x ∧ MlOk y)

theorem mlOkAlg : MlOkAlg := ⟨mulMlResult_ok, mulMlResult_ok_inv⟩

/-- The `pi`/`finalVerify` bridge: `pi` after a Miller loop is the pairing, `pi` is a
    homomorphism on `MlOk` values, and `finalVerify` decides equality of `pi`. The part of
    the pairing layer that mentions no G1/G2 operation, and so the part `blaster` can
    use. -/
def BridgeAlg : Prop :=
  (∀ (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element),
     pi (bls12_381_millerLoop p q) = e p q) ∧
  (∀ (x y : BLS12_381_MlResult), MlOk x → MlOk y → pi (x * y) = (pi x) * (pi y)) ∧
  (∀ (x y : BLS12_381_MlResult), bls12_381_finalVerify x y = true → pi x = pi y) ∧
  (∀ (x y : BLS12_381_MlResult), bls12_381_finalVerify x y = true → MlOk x ∧ MlOk y) ∧
  (∀ (x y : BLS12_381_MlResult),
     MlOk x → MlOk y → pi x = pi y → bls12_381_finalVerify x y = true)

theorem bridgeAlg : BridgeAlg :=
  ⟨pi_millerLoop, pi_mulMlResult, finalVerify_sound, finalVerify_ok, finalVerify_complete⟩

/-- The pairing on the subgroup: its discrete-log formula, its nondegeneracy, and the
    genuineness of a Miller loop on nonzero subgroup arguments. All three are
    `InG1`/`InG2`-guarded, which is no longer an obstacle: the guard is an uninterpreted
    predicate and the conclusions are over `e`, `pi`, the dlogs and the ℤ/r layer. -/
def PairingAlg : Prop :=
  (∀ (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element),
     InG1 p → InG2 q → e p q = gtGen ^ ((g1_dlog p) * (g2_dlog q))) ∧
  (∀ (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element),
     InG1 p → InG2 q → (e p q = gtOne ↔ (p = zeroG1 ∨ q = zeroG2))) ∧
  (∀ (p : BLS12_381_G1_Element) (q : BLS12_381_G2_Element),
     InG1 p → p ≠ 0 → InG2 q → q ≠ 0 → MlOk (bls12_381_millerLoop p q))

theorem pairingAlg : PairingAlg := ⟨e_dlog, e_nondegen, millerLoop_ok⟩

/-- Compression round-trips, and the subgroup guarantee `uncompress` provides. The last
    conjunct of each triple is the `vkInSubgroup` seam of
    `Tests/ReclaimGlobalV2Properties.lean`, and it now crosses inside `blaster`: the
    compress/uncompress builtins are `opaque`, hence uninterpreted functions, and the guard
    is an uninterpreted predicate. (The two middle conjuncts carry no guard and translated
    even while `InG1` was a `def`.) -/
def SerdeAlg : Prop :=
  (∀ (p : BLS12_381_G1_Element),
     InG1 p → bls12_381_G1_uncompress (bls12_381_G1_compress p) = Except.ok p) ∧
  (∀ (p : BLS12_381_G1_Element) (bs : ByteString),
     bls12_381_G1_uncompress bs = Except.ok p → bls12_381_G1_compress p = bs) ∧
  (∀ (p : BLS12_381_G1_Element) (bs : ByteString),
     bls12_381_G1_uncompress bs = Except.ok p → InG1 p) ∧
  (∀ (q : BLS12_381_G2_Element),
     InG2 q → bls12_381_G2_uncompress (bls12_381_G2_compress q) = Except.ok q) ∧
  (∀ (q : BLS12_381_G2_Element) (bs : ByteString),
     bls12_381_G2_uncompress bs = Except.ok q → bls12_381_G2_compress q = bs) ∧
  (∀ (q : BLS12_381_G2_Element) (bs : ByteString),
     bls12_381_G2_uncompress bs = Except.ok q → InG2 q)

theorem serdeAlg : SerdeAlg :=
  ⟨g1_uncompress_compress, g1_compress_uncompress, g1_uncompress_subgroup,
   g2_uncompress_compress, g2_compress_uncompress, g2_uncompress_subgroup⟩

/-- Eight *derived* facts that translate -- the point-free corner of the ℤ/r layer. Not part
    of `AllAlg`, and deliberately not part of `BlasterAlg`: every conjunct is a theorem
    proved above, so passing this bundle assumes nothing new, and mixing it into the axiom
    bundles would blur what this module assumes.

    Assuming nothing new is not the same as being free in the footprint. The proofs behind
    these theorems run through `g1_cyclic`, so a `blaster` proof off `DlogFacts` names the
    G1/G2 scalar-action axioms and `InG1_def` even when its goal mentions no point
    operation -- eleven axioms a `BlasterAlg`-only proof would not name.
    `Tests/AxiomsBlasterProbe.lean` pins exactly that footprint.

    Worth passing anyway, because `blaster` cannot re-derive any of them: `g1_dlog` is an
    uninterpreted function and the `∃` that would connect it to the generator is behind
    `InG1_def`. `g1_dlog_emod_eq_zero_iff` and `e_eq_iff_dlog` are the two that carry
    weight -- "a subgroup point is zero iff its dlog is 0 mod r" and "pairings agree iff the
    dlog products agree mod r" -- which together are the spine of the `acceptedPubUnique`
    argument in `Tests/OwnershipVerifyExample.lean`.

    What is *not* here, and why: `g1_cyclic`, `g1_dlog_add`, `g1_dlog_scalarMul_point`,
    `g1_emod_eq_zero_of_smul_gen`, `g1_zero_add`, `g1_add_right_cancel`, `g1_order` and
    `millerLoop_add_left_upto_finalVerify` all mention a `Cryptograph` point operation, so
    they hit the same wall as `G1Alg`. The pure ℤ/r lemmas (`gtPow_add`, `gtPow_emod`,
    `gtPow_inj_mod`, `emod_*`, `groupOrder_prime`) are absent for the opposite reason:
    `blaster` proves them from the definitions with no premise at all. -/
def DlogFacts : Prop :=
  (g1_dlog 0 = 0) ∧
  (g2_dlog 0 = 0) ∧
  (g1_dlog g1 = 1) ∧
  (g2_dlog g2 = 1) ∧
  (∀ (p : BLS12_381_G1_Element), InG1 p → (g1_dlog p % r = 0 ↔ p = 0)) ∧
  (∀ (q : BLS12_381_G2_Element), InG2 q → (g2_dlog q % r = 0 ↔ q = 0)) ∧
  (∀ (p p' : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
     InG1 p → InG2 q → InG1 p' → InG2 q' →
     (e p q = e p' q' ↔
        (g1_dlog p * g2_dlog q) % r = (g1_dlog p' * g2_dlog q') % r)) ∧
  (∀ (p p' : BLS12_381_G1_Element) (q q' : BLS12_381_G2_Element),
     InG1 p → p ≠ 0 → InG2 q → q ≠ 0 → InG1 p' → p' ≠ 0 → InG2 q' → q' ≠ 0 →
     (bls12_381_finalVerify (bls12_381_millerLoop p q) (bls12_381_millerLoop p' q') = true ↔
        e p q = e p' q'))

theorem dlogFacts : DlogFacts :=
  ⟨g1_dlog_zero, g2_dlog_zero, g1_dlog_gen, g2_dlog_gen,
   g1_dlog_emod_eq_zero_iff, g2_dlog_emod_eq_zero_iff,
   e_eq_iff_dlog, finalVerify_millerLoop_pair⟩

/-- The 18 axioms `blaster` can use with no ceremony at all, as one premise: everything whose
    conclusion mentions no G1/G2 *operation*. `InG1`/`InG2` guards are fine -- they are
    `opaque`, so the solver sees an uninterpreted predicate -- which leaves only `G1Alg` and
    `G2Alg` out, and those are reachable too in a module that seals the point instances
    (`Tests/AxiomsBlasterSealed.lean`). The
    premise to reach for in a route-C proof: `theorem foo_of (h : BlasterAlg) ... := by
    blaster`, then `foo_of blasterAlg`.

    Note what that costs in the footprint: `#print axioms` reports what the *premise*
    mentions, not what the solver used, so a proof off `BlasterAlg` names all 18 whether it
    needed them or not. Where the footprint is the point -- a pinned `#guard_msgs`, an audit
    of one obligation -- take the narrowest bundle that suffices instead. -/
def BlasterAlg : Prop := MlAlg ∧ MlOkAlg ∧ BridgeAlg ∧ PairingAlg ∧ SerdeAlg

theorem blasterAlg : BlasterAlg := ⟨mlAlg, mlOkAlg, bridgeAlg, pairingAlg, serdeAlg⟩

/-- Every Prop-typed axiom of this module, all 42. Exhaustive by construction: adding an
    axiom above without extending a bundle here leaves `#print axioms allAlg` an incomplete
    picture of what this file assumes, so extend it. The five data axioms -- `e`, `pi`,
    `MlOk`, `g1_dlog`, `g2_dlog` -- appear in that footprint anyway, since the bundles
    mention them. -/
def AllAlg : Prop :=
  G1Alg ∧ G2Alg ∧ MlAlg ∧ MlOkAlg ∧ PairingAlg ∧ BridgeAlg ∧ SerdeAlg

theorem allAlg : AllAlg :=
  ⟨g1Alg, g2Alg, mlAlg, mlOkAlg, pairingAlg, bridgeAlg, serdeAlg⟩

end Internal

export Internal
  ( -- constants
    r
    zeroG1
    zeroG2
    -- the order-r subgroup: the domain of every axiom below
    InG1
    InG2
    InG1_def
    InG2_def
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
    mkGT
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
    -- the axioms as bundles, with their witnesses
    G1Alg
    g1Alg
    G2Alg
    g2Alg
    MlAlg
    mlAlg
    MlOkAlg
    mlOkAlg
    BridgeAlg
    bridgeAlg
    PairingAlg
    pairingAlg
    SerdeAlg
    serdeAlg
    DlogFacts
    dlogFacts
    BlasterAlg
    blasterAlg
    AllAlg
    allAlg
  )

end PlutusCore.Crypto.BLS12_381.Axioms
