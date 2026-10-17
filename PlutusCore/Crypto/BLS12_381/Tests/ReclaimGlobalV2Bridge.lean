import PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample
import PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Properties

/-!
  # The artifact-level ownership properties

  `OwnershipVerifyExample.lean` proves six theorems about a model of the
  destination-reclaim verifier.  Four of them -- `groth16Holds_pairing`,
  `pairing_groth16Holds`, `pokHolds_pairing` and `acceptedPubUnique` -- never mention a
  program, being statements about `bls12_381_finalVerify`, `e` and `gtPow` for arbitrary
  parsed values, so they already apply verbatim to whatever this artifact parses.

  The other two, `destinationReclaimSound` and `destinationBinding`, are the security
  properties, and they are the ones for which "in terms of the actual program" means
  something: replace the hypothesis `verifyDestination vk pr pkh dest` with
  `reclaimAccepts m ctx`.  This module does that, at exactly the original generality, and
  in exchange takes on **one** assumption -- stated below and nowhere else.

  It is a separate module because a Prop-typed axiom declared beside a `blaster` call is
  harvested into every query in that module.  The bridge is Prop-typed, so declaring it in
  `ReclaimGlobalV2Properties` would push it into all twelve of the proved properties'
  queries.  It also draws the line where it belongs: that module contains what is proved
  about the artifact, this one the single thing that is assumed.

  ## What is still owed

  For a single reclaim slot, acceptance must force each of the following.  Discharging the
  bridge means proving all of them and composing.

  | # | obligation | status |
  |--:|------------|--------|
  | 1 | script purpose is rewarding | **proved** -- `success_requires_rewarding_purpose` |
  | 2 | a parameter reference input exists and is selected in range | **proved** |
  | 3 | the parameter NFT is the baked policy/token, quantity one | **proved** |
  | 4 | the parameter datum has the shape the decoder walks | **proved** |
  | 5 | the nine verifying-key slices decode to curve points | **proved** -- `vk*_ok` |
  | 6 | the claimed digest equals `blake2b_256(dom ‖ pkh ‖ destAddr)` | reachable |
  | 7 | the destination output covers the reclaimed input's value | plausibly reachable |
  | 8 | the 336-byte proof splits into A, B, C, commitment, PoK | **blocked** |
  | 9 | both `finalVerify` calls returned `true` on those values | blocked behind 8 |

  Obligation 8 is the whole of the gap, and it is blocked structurally rather than by
  effort: `sliceByteString` goes through `List Char`, and `Char → UInt32 → BitVec → Fin`
  is the same untranslatable-parameter wall `Fq1` used to hit -- this time in Lean core
  rather than in this repository.  Measured:
  `lengthOfByteString (sliceByteString 0 4 b) ≤ 4` for symbolic `b` fails with
  `Inductive datatype with instance parameters not supported: BitVec`.

  ## Honesty about the assumption

  `DenotesReclaim` is opaque and the bridge is an implication, so the pair is trivially
  consistent -- read `DenotesReclaim` as identically false and the axiom says nothing.
  Consistency is therefore *not* evidence that the bridge is true, exactly as with
  `PubScalarCollision` in the model file.  What the table buys is narrower and real: five
  of the nine obligations are discharged, one is measured as the sole blocker, and the
  assumption is stated once, in one place.

  Those five are proved as *facts about the artifact*, not as inputs to the two theorems
  below -- nothing can compose them into the bridge until rows 8 and 9 exist.  The pinned
  axiom footprints at the end of this file are what show it: `artifactReclaimSound` carries
  exactly the axioms of `destinationReclaimSound` plus the bridge, with no trace of them.
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Bridge

open PlutusCore.ByteString
open PlutusCore.Data (Data)
open PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample
open PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Properties

/-- `DenotesReclaim ctx pkh dest vk pr` — the context `ctx` is a well-formed single-slot
    reclaim of payment-key-hash `pkh` to destination `dest`, evaluated against verifying
    key `vk` and carrying `pr` as its only proof.

    Left abstract on purpose. Pinning it down means formalising the redeemer encoding, the
    58-byte destination address, the value-coverage requirement and the 336-byte proof
    layout — and that last item is obligation 8, the thing the bridge defers. A caller
    supplies this by construction: it says "the context I built really is the reclaim I
    claim it is", which is a statement about the *builder*, not about the artifact.

    `opaque` rather than `axiom` because an `X → Prop` axiom is harvested by
    `findLocalAxioms`; the inhabitant that `opaque` requires is not accessible, so this
    stays uninterpreted in every proof below. -/
opaque DenotesReclaim : Data → ByteString → ByteString → ParsedVK → ParsedProof → Prop := λ _ _ _ _ _ => True

/-- **The bridge — the one assumption in this module.**

    The compiled artifact implements the model's acceptance predicate: if it accepts a
    context that denotes a reclaim of `pkh` to `dest` under `vk` with proof `pr`, then
    that `vk`, `pr`, `pkh` and `dest` satisfy `verifyDestination`, i.e. both the Groth16
    equation and the BSB22 proof-of-knowledge equation held.

    This is the artifact-level analogue of what the model calls SNARK: there, Groth16
    knowledge soundness is assumed because it is not a curve consequence; here, that the
    program computes the verifier is assumed because obligation 8 is not reachable. See
    the module header for the obligation table and the discharge route. -/
axiom artifactImplementsVerifyDestination (m : Nat) (ctx : Data) (pkh dest : ByteString) (vk : ParsedVK) (pr : ParsedProof) :
  DenotesReclaim ctx pkh dest vk pr →
  IsHonestSetup vk →
  ProofWellFormed pr →
  reclaimAccepts m ctx
  ------------------------------------
  → verifyDestination vk pr pkh dest

/-! ## The two originals, over the actual program

    Both are the model theorem composed with the bridge. Neither weakens its original:
    the quantifiers, the hypotheses on `vk` and `pr`, and the conclusions — including the
    collision disjunct — are unchanged. `m` is universally quantified, so neither says
    anything about a particular fuel. -/

/-- **Ownership soundness, for the compiled artifact.** If the artifact accepts a
    transaction reclaiming to `dest` on behalf of payment-key-hash `pkh`, then the
    submitter knew a master key and derivation path producing exactly `pkh` — i.e.
    controls the Cardano key — unless a collision in the public-input encoding is
    exhibited.

    Same statement as `destinationReclaimSound`, with acceptance by the real program in
    place of the model's `verifyDestination`. -/
theorem artifactReclaimSound
  (m : Nat) (ctx : Data) (pkh dest : ByteString) (vk : ParsedVK) (pr : ParsedProof)
  (hden : DenotesReclaim ctx pkh dest vk pr)
  (hvk : IsHonestSetup vk) (hwf : ProofWellFormed pr)
  (hacc : reclaimAccepts m ctx) :
    (∃ xprv path, deriveCredential xprv path = pkh) ∨ (∃ c d, PubScalarCollision c d pkh dest) :=
      by
        exact destinationReclaimSound vk pr pkh dest hvk hwf (artifactImplementsVerifyDestination m ctx pkh dest vk pr hden hvk hwf hacc)

/-- **Destination binding, for the compiled artifact.** One proof cannot authorise two
    statements: if the artifact accepts two transactions carrying the *same* proof `pr`
    but reclaiming `(pkh, dest)` and `(pkh', dest')`, those statements coincide — unless
    a collision is exhibited. A valid proof sitting in the mempool cannot be re-pointed
    at another destination.

    Same statement as `destinationBinding`. Note the two acceptances may be observed at
    different fuels `m` and `m'` and in different contexts `ctx` and `ctx'`; all that is
    shared is the proof. -/
theorem artifactDestinationBinding
  (m m' : Nat) (ctx ctx' : Data) (pkh dest pkh' dest' : ByteString)
  (vk : ParsedVK) (pr : ParsedProof)
  (hden  : DenotesReclaim ctx  pkh  dest  vk pr)
  (hden' : DenotesReclaim ctx' pkh' dest' vk pr)
  (hvk : IsHonestSetup vk) (hwf : ProofWellFormed pr)
  (hacc  : reclaimAccepts m  ctx)
  (hacc' : reclaimAccepts m' ctx') :
    (pkh = pkh' ∧ dest = dest') ∨ PubScalarCollision pkh dest pkh' dest' :=
      by
        exact destinationBinding vk pr pkh dest pkh' dest' hvk hwf
          (artifactImplementsVerifyDestination m  ctx  pkh  dest  vk pr hden  hvk hwf hacc)
          (artifactImplementsVerifyDestination m' ctx' pkh' dest' vk pr hden' hvk hwf hacc')

/-! The footprints.  Neither names any of the eight gates or the nine `vk*_ok` facts: the
    obligations discharged in `ReclaimGlobalV2Properties.lean` are not inputs to these two
    theorems, and cannot be until rows 8 and 9 of the table exist. -/

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Bridge.artifactReclaimSound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.IsHonestSetupCore,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.MasterXprv,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.Path,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.ProofWellFormedBytes,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.PubScalarCollision,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.byteStringToIntegerBE,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.byteStringToIntegerLE,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.deriveCredential,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.destinationDigest,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.expandMsgXmd48,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.groth16KnowledgeSoundness,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.pubScalar_collision_dichotomy,
 PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Bridge.artifactImplementsVerifyDestination]
-/
#guard_msgs in
#print axioms artifactReclaimSound

/--
info: 'PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Bridge.artifactDestinationBinding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.InG1_def,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.InG2_def,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.MlOk,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.e,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.e_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.e_nondegen,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.finalVerify_ok,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.finalVerify_sound,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_dlog_scalarMul,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_add_scalar,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_mod,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_mul,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_one,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g1_scalarMul_zero,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_dlog,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_dlog_scalarMul,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_mod,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_one,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.g2_scalarMul_zero,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.mulMlResult_ok_inv,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi_millerLoop,
 PlutusCore.Crypto.BLS12_381.Axioms.Internal.pi_mulMlResult,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.IsHonestSetupCore,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.ProofWellFormedBytes,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.PubScalarCollision,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.byteStringToIntegerBE,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.byteStringToIntegerLE,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.destinationDigest,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.expandMsgXmd48,
 PlutusCore.Crypto.BLS12_381.Tests.OwnershipVerifyExample.pubScalar_collision_dichotomy,
 PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Bridge.artifactImplementsVerifyDestination]
-/
#guard_msgs in
#print axioms artifactDestinationBinding

end PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Bridge
