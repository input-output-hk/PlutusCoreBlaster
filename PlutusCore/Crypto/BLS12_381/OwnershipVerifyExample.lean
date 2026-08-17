import Cryptograph.BLS12_381.Basic

import PlutusCore.Crypto.BLS12_381.Axioms

/-
  Single destination reclaim -- worked example over the BLS12-381 axioms.

  Models one path end to end:
    * the circuit `root-ownership-destination-v2/bls12-381/groth16`, and
    * the on-chain committed-Groth16 check that accepts its proofs.

  Three disjoint assumption classes are kept visibly separate:
    * CURVE  -- the Axioms module, whose group/pairing axioms hold only on the
                order-r subgroup (`InG1`/`InG2`); `vkInSubgroup` and
                `proofInSubgroup` below carry that for the parsed points, and on
                chain they are discharged by `g*_uncompress_subgroup`.
                Consumed via the pairing bridge -- `finalVerify_sound` +
                `finalVerify_ok` (acceptance implies every Miller-loop value is a
                genuine Fq12 unit, `MlOk`), then `pi_mulMlResult` and
                `pi_millerLoop` -- and the group + scalar-action laws;
                destination binding additionally needs
                the ℤ/r picture of the three groups: `g*_cyclic` +
                `g*_dlog_scalarMul` + `g*_scalarMul_mod`, `e_dlog` +
                `gtPow_inj_mod` (⟨gtGen⟩ of order exactly r), and `e_add_left` /
                `e_nondegen` -- from which `gtPow_add` and `groupOrder_prime`
                (no zero divisors mod r) are *derived*, not assumed. No
                serialization axiom is used, and nothing depends on
                `g*_order`, hence not on `decide +native`.
    * HASH   -- blake2b_256 / expand_message_xmd as opaque functions; exactly one
                fact is used (`pubScalar_injective`).
    * SNARK  -- Groth16(+BSB22) knowledge soundness (`groth16KnowledgeSoundness`):
                the extractor. NOT a consequence of the curve axioms.
-/

namespace PlutusCore.Crypto.BLS12_381.OwnershipVerifyExample

open Cryptograph.BLS12_381

open PlutusCore.ByteString
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Crypto.BLS12_381.Pairing
open PlutusCore.Crypto.BLS12_381.Axioms

/- Byte / hash layer (HASH assumptions, tracked separately).
   Modeled opaquely: the reclaim argument consumes only `pubScalar_injective`. -/

axiom bsLen                 : ByteString → Int
axiom byteStringToIntegerLE : ByteString → Int
axiom byteStringToIntegerBE : ByteString → Int

/- `destinationDigest pkh dest = blake2b_256("ROOT-OWNERSHIP-DESTINATION-v1" ‖ pkh ‖ dest)`. -/
axiom destinationDigest : ByteString → ByteString → ByteString
/- RFC 9380 expand_message_xmd (SHA-256, DST "bsb22-commitment", 48-byte output) over the 96-byte uncompressed commitment. -/
axiom expandMsgXmd48 : ByteString → ByteString

/- The Groth16 public-input scalar: LITTLE-ENDIAN read of the digest, reduced mod r. -/
noncomputable def pubScalar (pkh dest : ByteString) : Int :=
  byteStringToIntegerLE (destinationDigest pkh dest) % r

/- The BSB22 commitment challenge: BIG-ENDIAN read of the xmd hash, reduced mod r. -/
noncomputable def eCmtScalar (commitmentBytes : ByteString) : Int :=
  byteStringToIntegerBE (expandMsgXmd48 commitmentBytes) % r

/- Parsed verifying key and proof (after `uncompress`, so all points in the order-r subgroup).
   Byte slicing / length 672 / 336 / canonical-Y are folded into `ProofWellFormed`. -/

structure ParsedVK where
  alpha : BLS12_381_G1_Element
  beta  : BLS12_381_G2_Element
  gamma : BLS12_381_G2_Element
  delta : BLS12_381_G2_Element
  ic0   : BLS12_381_G1_Element
  ic1   : BLS12_381_G1_Element
  k2    : BLS12_381_G1_Element
  ckG   : BLS12_381_G2_Element     -- commitment key,           G2
  ckGSN : BLS12_381_G2_Element     -- commitment key · (−σ),    G2  (PoK companion)

structure ParsedProof where
  a               : BLS12_381_G1_Element
  b               : BLS12_381_G2_Element
  c               : BLS12_381_G1_Element
  commitmentBytes : ByteString              -- 96-byte uncompressed X‖Y  (proof[192:288])
  commitment      : BLS12_381_G1_Element    -- decoded point (sort-bit reconstruct ∘ uncompress)
  pok             : BLS12_381_G1_Element    -- proof[288:336]

/- Every parsed point lies in the order-r subgroup -- the domain on which the
   curve axioms hold at all. On chain this is not an assumption but a
   consequence: each point is produced by `uncompress`, and
   `g1_uncompress_subgroup` / `g2_uncompress_subgroup` deliver exactly this. -/
def vkInSubgroup (vk : ParsedVK) : Prop :=
  InG1 vk.alpha ∧ InG2 vk.beta  ∧ InG2 vk.gamma ∧ InG2 vk.delta ∧
  InG1 vk.ic0   ∧ InG1 vk.ic1   ∧ InG1 vk.k2    ∧ InG2 vk.ckG   ∧ InG2 vk.ckGSN

def proofInSubgroup (pr : ParsedProof) : Prop :=
  InG1 pr.a ∧ InG2 pr.b ∧ InG1 pr.c ∧ InG1 pr.commitment ∧ InG1 pr.pok

/- Structural acceptance gate: length 336, canonical `Y < p`, and every point a
   canonically-decoded order-r element, with `commitmentBytes` decoding to `commitment`.
   The byte-level conjuncts stay opaque (they discharge from the Verify.hs byte
   checks); the subgroup conjunct is spelled out, because every curve axiom below
   needs it and `g1_uncompress_subgroup` is what supplies it. -/
axiom ProofWellFormedBytes : ParsedProof → Prop

def ProofWellFormed (pr : ParsedProof) : Prop :=
  ProofWellFormedBytes pr ∧ proofInSubgroup pr

/- The aggregated public-input commitment vkX = IC₀ + pub·IC₁ + eCmt·K₂ + commitment. -/
def vkX (vk : ParsedVK) (pub eCmt : Int) (commitment : BLS12_381_G1_Element) : BLS12_381_G1_Element :=
  vk.ic0 + pub * vk.ic1 + eCmt * vk.k2 + commitment

abbrev ML := bls12_381_millerLoop

/- Groth16 acceptance:  ML(A,B)  ==  ML(α,β) · ML(vkX,γ) · ML(C,δ)  under finalVerify.
   (`groth16VerifyCommittedParsed`, Verify.hs:775–784.) -/
def groth16Holds (vk : ParsedVK) (pr : ParsedProof) (pub eCmt : Int) : Prop :=
  let α   := vk.alpha
  let β   := vk.beta
  let γ   := vk.gamma
  let δ   := vk.delta
  let a   := pr.a
  let b   := pr.b
  let c   := pr.c
  let vkx := vkX vk pub eCmt pr.commitment
  ----------------------------------------
  bls12_381_finalVerify (ML a b) (ML α β * ML vkx γ * ML c δ) = true

/- BSB22 commitment proof-of-knowledge:  ML(pok, ckG) == ML(−commitment, ckGSN).
   (`verifyCommittedProofPokBatch`, Verify.hs:661–673.) -/
def pokHolds (vk : ParsedVK) (pr : ParsedProof) : Prop :=
  let ckG        := vk.ckG
  let ckGSN      := vk.ckGSN
  let pok        := pr.pok
  let commitment := pr.commitment
  -------------------------------
  bls12_381_finalVerify (ML pok ckG) (ML (-commitment) ckGSN) = true

/- The full on-chain acceptance: recompute `pub` from the on-chain `(pkh, dest)` and
   `eCmt` from the proof's own commitment bytes, then require BOTH checks. -/
def verifyDestination (vk : ParsedVK) (pr : ParsedProof) (pkh dest : ByteString) : Prop :=
  groth16Holds vk pr (pubScalar pkh dest) (eCmtScalar pr.commitmentBytes) ∧ pokHolds vk pr

/- Meaning in G_T (CURVE), SOUNDNESS direction — the one the verifier is used in, and the one consumed below.
   It needs no side conditions: acceptance itself implies that every Miller-loop value in the check is a genuine
   Fq12 unit, which is exactly what makes `pi` multiplicative on them.
   The chain is `finalVerify_sound`, `pi_mulMlResult` and `pi_millerLoop` -/
theorem groth16Holds_pairing (vk : ParsedVK) (pr : ParsedProof) (pub eCmt : Int) (h : groth16Holds vk pr pub eCmt) :
  let α   := vk.alpha
  let β   := vk.beta
  let γ   := vk.gamma
  let δ   := vk.delta
  let a   := pr.a
  let b   := pr.b
  let c   := pr.c
  let cmt := pr.commitment
  let vkx := vkX vk pub eCmt cmt
  ------------------------------
  e a b = e α β * e vkx γ * e c δ :=
    by
      rw [groth16Holds] at h
      have ⟨_, hR⟩   := finalVerify_ok _ _ h
      have ⟨h₁₂, h₃⟩ := mulMlResult_ok_inv _ _ hR
      have ⟨h₁, h₂⟩  := mulMlResult_ok_inv _ _ h₁₂
      have hgt       := finalVerify_sound _ _ h
      rwa [pi_mulMlResult _ _ h₁₂ h₃, pi_mulMlResult _ _ h₁ h₂,
           pi_millerLoop, pi_millerLoop, pi_millerLoop, pi_millerLoop] at hgt

/- The converse. Unlike soundness it is conditional:
   a Miller loop at the identity is `none`, on which `finalVerify` reports failure however the pairings compare,
   so the four values must be known genuine (`millerLoop_ok`: nonzero subgroup arguments). -/
theorem pairing_groth16Holds (vk : ParsedVK) (pr : ParsedProof) (pub eCmt : Int)
    (hab : MlOk (ML pr.a pr.b))
    (hαβ : MlOk (ML vk.alpha vk.beta))
    (hxγ : MlOk (ML (vkX vk pub eCmt pr.commitment) vk.gamma))
    (hcδ : MlOk (ML pr.c vk.delta))
    (hp : e pr.a pr.b = e vk.alpha vk.beta * e (vkX vk pub eCmt pr.commitment) vk.gamma * e pr.c vk.delta) :
  groth16Holds vk pr pub eCmt :=
    by
      rw [groth16Holds]
      refine finalVerify_complete _ _ hab (mulMlResult_ok _ _ (mulMlResult_ok _ _ hαβ hxγ) hcδ) ?_
      rw [pi_mulMlResult _ _ (mulMlResult_ok _ _ hαβ hxγ) hcδ, pi_mulMlResult _ _ hαβ hxγ, pi_millerLoop, pi_millerLoop, pi_millerLoop, pi_millerLoop]
      exact hp

/- The PoK side is the same chain without the product step -- exactly what the
   exported `finalVerify_millerLoop_pair_sound` states. -/
theorem pokHolds_pairing (vk : ParsedVK) (pr : ParsedProof) (h : pokHolds vk pr) :
  let σ   := vk.ckGSN
  let ck  := vk.ckG
  let pok := pr.pok
  let cmt := pr.commitment
  ------------------------
  e pok ck = e (-cmt) σ :=
    by
      rw [pokHolds] at h
      exact finalVerify_millerLoop_pair_sound _ _ _ _ h

/- The circuit statement (WHAT the prover must know).
   `Circuit.Define` constrains a private witness (masterXprv, path, destination):
     1. Icarus master clamp on kL,
     2. CKD along m/1852'/1815'/account'/role/index → leaf scalar kL_leaf,
     3. credential = blake2b224(compress(kL_leaf · B))      (Cardano payment key hash),
     4. Pub = LE→field(blake2b256(dom ‖ credential ‖ destination)) mod r.
   Steps 1–3 (Ed25519/CKD/blake2b) are orthogonal to the curve axioms and are collapsed into one opaque `deriveCredential`;
   only its being a FUNCTION of the secret is used. (ckd.DeriveChain ▸ ownership.Credential.) -/

axiom MasterXprv : Type
axiom Path       : Type
axiom deriveCredential : MasterXprv → Path → ByteString

/- The relation `R(Pub)` the destination R1CS proves satisfiable. -/
def circuitStatement (pub : Int) : Prop :=
  ∃ (xprv : MasterXprv) (path : Path) (dest : ByteString),
  --------------------------------------------------------
  bsLen dest = 58 ∧ pub = pubScalar (deriveCredential xprv path) dest

/- Groth16(+BSB22) knowledge soundness (SNARK assumption; NOT a curve consequence).
   `vk` is the honest CRS for this circuit — on-chain, the parameter-bound,
   hash-pinned 672-byte key. -/

axiom IsHonestSetupCore : ParsedVK → Prop

/- An honest key has its points in the order-r subgroup (as parsed by `uncompress`)
   and is NON-DEGENERATE in the two slots the curve algebra needs: γ ≠ O  and  IC₁ ≠ O.
   (Setup draws γ, δ ← ℤ_r^*, so γ = γ·g2 ≠ O; and IC₁ = γ⁻¹·(β·u₁(τ) + α·v₁(τ) + w₁(τ))
   is the basis point of the single public input, nonzero for this circuit.)
   Spelled out as part of the predicate rather than bought with extra axioms, because it is exactly what
   distinguishes the pinned key from a malicious one: a key with IC₁ = O accepts every `pub`, which is precisely
   what `acceptedPubUnique` below cannot and must not prove.
   `groth16KnowledgeSoundness` only gains a hypothesis this way, so it becomes a weaker assumption, not a stronger one. -/
def IsHonestSetup (vk : ParsedVK) : Prop :=
  IsHonestSetupCore vk ∧ vkInSubgroup vk ∧ vk.gamma ≠ 0 ∧ vk.ic1 ≠ 0

axiom groth16KnowledgeSoundness (vk : ParsedVK) (pr : ParsedProof) (pkh dest : ByteString) :
  IsHonestSetup vk →
  ProofWellFormed pr →
  verifyDestination vk pr pkh dest
  -----------------------------------
  → circuitStatement (pubScalar pkh dest)

/- Collision resistance of the public-input encoding, in the only form used:
   `(cred, dest) ↦ pubScalar cred dest` is injective on canonical inputs.
   (blake2b-256 CR + injective LE-mod-r read.) A HASH-layer assumption. -/
axiom pubScalar_injective (c d c' d' : ByteString) :
  pubScalar c d = pubScalar c' d' → c = c' ∧ d = d'

/- Ownership soundness (WHAT it ensures).
   An accepted proof for a reclaim of payment-key-hash `pkh` to destination `dest` implies the prover
   KNEW a master key + path deriving to exactly `pkh` -- i.e. controls the Cardano key.
   (extractor ⇒ ∃ witness with pubScalar(cred) dest' = pubScalar pkh dest; `pubScalar_injective` ⇒ cred = pkh.)
   Note the assumption footprint: this theorem consumes NO curve axiom at all -- the curve content sits inside `groth16KnowledgeSoundness`.
   The curve algebra is done separately, in `acceptedPubUnique`. -/
theorem destinationReclaimSound (vk : ParsedVK) (pr : ParsedProof) (pkh dest : ByteString) (hvk : IsHonestSetup vk) (hwf : ProofWellFormed pr) (hverify : verifyDestination vk pr pkh dest) :
  ∃ xprv path, deriveCredential xprv path = pkh :=
    by
      have ⟨xprv, path, _, _, hpub⟩ := groth16KnowledgeSoundness vk pr pkh dest hvk hwf hverify
      have ⟨hc, _⟩ := pubScalar_injective _ _ _ _ hpub.symm
      exists xprv, path

/- Uniqueness of the accepted public input for a FIXED proof -- the curve-algebra core of destination binding. With `pr` fixed, `finalVerify` pins `e(vkX,γ)`;
   γ non-degeneracy pins `vkX`; `IC₁` of order r pins `pub` mod r.
   Consumes the bridge (`finalVerify_iff`, `pi_mulMlResult`, `pi_millerLoop`) plus the ℤ/r picture -- `e_dlog` + `gtPow_inj_mod` (via `gtPow_add`) and
   `emod_cancel_mul_right` (⇐ `groupOrder_prime` ⇐ `e_nondegen`) over the group and scalar-action laws.
   No HASH and no SNARK assumption enters.

   The two non-degeneracy hypotheses are necessary, not bookkeeping.
   With `IC₁ = O` the aggregated `vkX` does not mention `pub` at all; with `γ = O`,
   `e_nondegen` makes `e(vkX,γ) = 1` for every `vkX`, so the aggregated point
   drops out of the equation entirely.
   Either way one proof accepts every public input and the conclusion is plainly false.
   On chain both come from the parameter-bound, hash-pinned key, via `IsHonestSetup` (see `destinationBinding`). -/
theorem acceptedPubUnique (vk : ParsedVK) (pr : ParsedProof) (pub eCmt pub' : Int) (hvk : vkInSubgroup vk) (hpr : proofInSubgroup pr) (hγ : vk.gamma ≠ 0) (hic1 : vk.ic1 ≠ 0) (h : groth16Holds vk pr pub eCmt) (h' : groth16Holds vk pr pub' eCmt) :
  pub % r = pub' % r :=
    by
      have ⟨hα, hβ, hγm, hδ, hic0, hic1m, hk2, _, _⟩ := hvk
      have ⟨_, _, hc, hcmt, _⟩ := hpr
      -- (0) the aggregated point stays in the subgroup, whatever the public input,
      --     so the curve axioms apply to it.
      have hagg : ∀ p : Int, InG1 (vkX vk p eCmt pr.commitment) := λ p =>
        InG1_add _ _ (InG1_add _ _ (InG1_add _ _ hic0 (InG1_smul _ _ hic1m))
          (InG1_smul _ _ hk2)) hcmt
      -- (1) read both acceptances in G_T: e(A,B) = e(α,β)·e(vkX,γ)·e(C,δ).
      have hp  := groth16Holds_pairing vk pr pub  eCmt h
      have hp' := groth16Holds_pairing vk pr pub' eCmt h'
      -- (2) e(A,B) is shared, so the two right-hand sides agree; `e_dlog` turns
      --     each pairing into a power of gtGen, `gtPow_add` collapses the product
      --     and `gtPow_inj_mod` lands the whole equation in ℤ/r.
      have hcomb := hp.symm.trans hp'
      rw [e_dlog _ _ hα hβ, e_dlog _ _ (hagg pub) hγm, e_dlog _ _ (hagg pub') hγm, e_dlog _ _ hc hδ] at hcomb
      simp only [← gtPow_add] at hcomb
      rw [gtPow_inj_mod] at hcomb
      -- (3) the e(α,β) and e(C,δ) exponents are shared: cancel them, then cancel
      --     dlog γ ≠ 0 (γ non-degeneracy) to pin the aggregated point itself.
      have hX : (g1_dlog (vkX vk pub  eCmt pr.commitment) * g2_dlog vk.gamma) % r
              = (g1_dlog (vkX vk pub' eCmt pr.commitment) * g2_dlog vk.gamma) % r := emod_eq_of_sub_eq hcomb (by omega)
      have hV := emod_cancel_mul_right _ _ _ (mt (g2_dlog_emod_eq_zero_iff vk.gamma hγm).mp hγ) hX
      -- (4) dlog is additive on IC₀ + pub·IC₁ + eCmt·K₂ + commitment, so `pub`
      --     survives multiplied by dlog IC₁ ≠ 0; cancel that too.
      have hvkX : ∀ p : Int,
        g1_dlog (vkX vk p eCmt pr.commitment) % r
        = (g1_dlog vk.ic0 + p * g1_dlog vk.ic1 + eCmt * g1_dlog vk.k2 + g1_dlog pr.commitment) % r :=
          by
            intro p
            have h₁ : InG1 (vk.ic0 + p * vk.ic1)                := InG1_add _ _ hic0 (InG1_smul _ _ hic1m)
            have h₂ : InG1 (vk.ic0 + p * vk.ic1 + eCmt * vk.k2) := InG1_add _ _ h₁   (InG1_smul _ _ hk2)
            rw [vkX, g1_dlog_add _ _ h₂ hcmt, g1_dlog_add _ _ h₁ (InG1_smul _ _ hk2), g1_dlog_add _ _ hic0 (InG1_smul _ _ hic1m),
                g1_dlog_scalarMul_point _ _ hic1m, g1_dlog_scalarMul_point _ _ hk2]
            simp only [Int.emod_add_emod, Int.add_emod_emod, Int.emod_emod]
      rw [hvkX pub, hvkX pub'] at hV
      exact emod_cancel_mul_right _ _ _ (mt (g1_dlog_emod_eq_zero_iff vk.ic1 hic1m).mp hic1) (emod_eq_of_sub_eq hV (by omega))

/- Destination binding (anti-front-running). One proof cannot authorize two
   statements: `eCmt` depends only on `pr.commitmentBytes`, so both accept under
   the same `eCmt`; `acceptedPubUnique` equates the (already reduced) public
   scalars; `pubScalar_injective` finishes. A valid proof in the mempool cannot be
   re-pointed to another destination — the reason `Pub` hashes `dest` in. -/
theorem destinationBinding (vk : ParsedVK) (pr : ParsedProof) (pkh dest pkh' dest' : ByteString)
    (hvk : IsHonestSetup vk) (hwf : ProofWellFormed pr)
    (h : verifyDestination vk pr pkh dest) (h' : verifyDestination vk pr pkh' dest') :
  pkh = pkh' ∧ dest = dest' :=
    by
      -- from h.1, h'.1: groth16Holds vk pr (pubScalar ·) (eCmtScalar pr.commitmentBytes)
      -- — the SAME eCmt, because it is derived from the proof's own commitment bytes
      -- and nothing else. So `acceptedPubUnique` applies to the one fixed proof.
      have hmod := acceptedPubUnique vk pr _ _ _ hvk.2.1 hwf.2 hvk.2.2.1 hvk.2.2.2 h.1 h'.1
      -- `pubScalar` is already reduced mod r, so the congruence is an equality;
      -- then collision resistance of the public-input encoding finishes.
      have hred : ∀ c d : ByteString, pubScalar c d % r = pubScalar c d := by intro c d; simp only [pubScalar, Int.emod_emod]
      rw [hred, hred] at hmod
      exact pubScalar_injective _ _ _ _ hmod

end PlutusCore.Crypto.BLS12_381.OwnershipVerifyExample
