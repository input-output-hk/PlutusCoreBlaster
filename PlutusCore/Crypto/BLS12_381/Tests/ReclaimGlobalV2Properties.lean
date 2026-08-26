import Blaster

import PlutusCore.UPLC.CekMachine.Lemmas
import PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2

/-!
  # Properties of the compiled `reclaim-global-v2` artifact

  `OwnershipVerifyExample.lean` proves `destinationReclaimSound`, `destinationBinding`
  and `acceptedPubUnique` about a *hand-written model* of the destination-reclaim
  verifier. This module proves properties of the **compiled artifact** instead, using
  `#import_uplc` / `#prep_uplc` / `blaster`, and records exactly where that becomes
  impossible and why.

  ## What is proved here

  Eight gates, one per row of the table under **Measured structure** below. Each comes as
  a pair: a `*_gate` theorem universally quantified over the value that gate inspects,
  and a `success_requires_*` corollary that drops the fuel by way of `atAnyFuel`. The
  symbolic holes span `Integer`, `ByteString`, `Data` and `List Data`, so together they
  say the parameter-NFT authentication holds against *any* attempted substitution: no
  other policy id and no other token name is accepted, the quantity must be exactly one,
  and the parameters must arrive as a well-shaped inline datum.

  Three supporting results:

  * `good_params_not_yet_errored` — the non-vacuity anchor. On a well-formed parameter
    section the artifact has *not* errored by `probeFuel`, so every gate premise above is
    satisfiable rather than empty.
  * `base_script_hash_unchecked`, `params_datum_tag_unchecked` — two things the artifact
    does *not* check, each found by the corresponding gate coming back falsifiable.
    Neither is exploitable on chain; see **LEDGER**.
  * `prepared_never_halts` — no `isSuccessful`-shaped theorem about this artifact can be
    non-vacuous, which is why everything here is phrased via `erroredWithin`.

  All of the above are proved by `blaster`. The nine `vk*_ok` decoding facts that the
  three supporting results lean on are not, and cannot be — see **SMT**.

  For the two *model* security properties restated over this artifact, see
  `ReclaimGlobalV2Bridge.lean`; it depends on this module and on one named assumption.

  ## Correspondence with `OwnershipVerifyExample.lean`

  Mostly empty, on purpose. `OwnershipVerifyExample` takes a parsed `vk`, a parsed `pr`,
  a `pkh` and a `dest` as *given* and reasons about `verifyDestination vk pr pkh dest`.
  This module reasons about everything that happens *before* those four values exist:
  which script is running, how the transaction is shaped, where the parameters come from.
  The two meet at exactly one seam, the parsed verifying key.

  **The two real correspondences.**

  | `OwnershipVerifyExample` | here |
  |---|---|
  | the nine conjuncts of `vkInSubgroup`, of which it says "on chain this is not an assumption but a consequence: each point is produced by `uncompress`" | `vkG1_*_ok` / `vkG2_*_ok` — those nine `uncompress` calls, on this artifact's own baked bytes, do succeed. Slice-to-field map tabulated and verified below. Compose with `g*_uncompress_subgroup` and this *is* `vkInSubgroup` for this key. |
  | the premise it never states — that the code under discussion is the reclaim script at all, invoked as a withdrawal | `success_requires_rewarding_purpose` |

  **Model results with no counterpart here: all six.**
  `groth16Holds_pairing`, `pairing_groth16Holds` and `pokHolds_pairing` are about
  `bls12_381_finalVerify` applied to Miller loops, and `destinationReclaimSound` and
  `destinationBinding` rest on those plus `groth16KnowledgeSoundness`. Nothing here
  reaches either pairing check (**REACH**), so those five have no analogue in this file.
  `acceptedPubUnique` is a different case: pure curve algebra about `e`, `g*_dlog` and
  `gtPow`, not a statement about a program, so it could have no counterpart here even if
  the whole validator were reachable.

  Unmatched on the assumption side too. `ProofWellFormedBytes` (the 336-byte width and
  canonical-Y checks), the on-chain recomputation of `pubScalar` from `(pkh, dest)` and
  `eCmtScalar`'s `expand_message_xmd` all sit behind `parseVerifyingKeyBatch`; and
  `IsHonestSetupCore`, `vk.gamma ≠ 0`, `vk.ic1 ≠ 0`, `groth16KnowledgeSoundness` and
  `pubScalar_collision_dichotomy` are cryptographic or trust-in-setup assumptions, which
  no property of a program can discharge.

  **Results here with no counterpart in the model: nearly all of them.** The model has no
  notion of a transaction, so the parameter-NFT authentication, the reference-index and
  destination-index bounds, and the two permissiveness findings are all invisible to it.
  `prepared_never_halts` and `good_params_not_yet_errored` are methodological and have no
  model analogue either — as is the `erroredWithin` machinery they rest on, which is
  generic to the CEK machine and lives in `PlutusCore/UPLC/CekMachine/Lemmas.lean`.

  **One thing this map does not claim.** The parameter NFT does **not** authenticate the
  verifying key, so no gate here discharges any part of `IsHonestSetup`.
  `decodeValidatedParams` returns the *base script hash* — which inputs count as reclaim
  inputs. The verifying key is a baked script parameter, hash-pinned at export time and
  never re-hashed on chain; that those baked bytes are the honest CRS is exactly the
  **IDENTITY** assumption, and it stays one.

  ## Measured structure of the artifact

  Step counts at which the artifact first reaches `State.Error`, measured by bisection
  on the concrete CEK machine (all contexts as built below):

  | context                                       | first error step |
  |-----------------------------------------------|-----------------:|
  | wrong script purpose (tag 0, 1, 5)            |              450 |
  | destination-output start index past outputs   |              798 |
  | no reference inputs at all                    |              863 |
  | parameter reference index out of range        |              984 |
  | wrong parameter policy id                     |             1256 |
  | parameter NFT quantity ≠ 1                    |             1334 |
  | wrong parameter token name                    |             1373 |
  | parameter datum missing / a hash              |        1382/1383 |
  | **all parameter gates pass**                  |         **1674** |

  Three things follow.

  First, the whole validator traverses in ~1700 CEK steps, not the ~2,000,000 a naive
  bound suggests: `uncompress`, `millerLoop` and `finalVerify` are single builtin
  applications, so the BLS field arithmetic costs wall-clock rather than steps.

  Second, any fuel strictly between 1383 and 1674 makes every gate simultaneously
  non-vacuous — the good path has not errored yet, every bad one has. That is
  `probeFuel = 1390`, used by every gate. (`#prep_uplc` deliberately uses 1700 instead;
  see the comment at its call site.)

  Third, execution order is not source order. The destination-output start index is
  checked at step 798, *before* the parameter gates, even though `dropAtData` follows
  `parseVerifyingKeyBatch` in the Haskell `let` block. So "before the verifying key is
  parsed" describes none of these gates correctly: on the source reading `dropAtData`
  comes after it, and on the execution reading seven of the eight fire after the first
  `uncompress` at step 489 — only the purpose gate, at 450, precedes it.

  ## Assumption ledger

  Extends the CURVE / HASH / SNARK classes of `OwnershipVerifyExample.lean`.

  * **BLS-UNINTERPRETED.** Since `Fq1` became `Nat`-backed the BLS *types* translate to
    SMT (see `Tests/BlasterSmoke.lean`), but the *operations* stay uninterpreted
    `declare-fun`s: Z3 gets congruence and a codomain constraint, never a group law.
    Nothing here says anything about the curve.
  * **REACH.** `bls12_381_G1_uncompress` is Lean `opaque`, so the Blaster optimizer cannot
    reduce it even on the artifact's own concrete verifying key. Past step 489 the residual
    therefore carries an unreduced `Except String BLS12_381_G1_Element`, and anything
    downstream sits behind an `is-Except.ok` test on an *uninterpreted* function.

    What decides whether a goal is provable is therefore not whether the builtin is
    reached, but whether the goal *depends* on its result. The eight gates do not: each
    reaches its verdict for a reason that holds whichever way the decode goes, so the
    optimizer folds both branches and they need no premise. The three statements that the
    machine has *not* errored do depend on it, and take `VkDecodes` as a premise.

    Nothing here reaches the Groth16 or proof-of-knowledge equations at all. What blocks
    that is the 336-byte proof: `sliceByteString` is `bs.data.toList.drop s |>.take k`, so
    a symbolic proof goes through `List Char`, and `Char → UInt32 → BitVec → Fin` is
    untranslatable. See `ReclaimGlobalV2Bridge.lean` for the full obligation table.
  * **BLASTER.** Two Blaster defects had to be fixed upstream before any of this
    translated, both found here and neither BLS-specific. Both are now fixed, so the
    `lakefile` pin is what this module's translatability rests on:
      1. `generateUndeclaredFun` looked the codomain well-formedness predicate up under
         the *unreduced* return type, while the predicate is registered under the reduced
         one, so any `opaque` whose signature named an `abbrev` aborted with
         `createPredQualifierAppAux: predicate declaration expected` — which is every one
         of the BLS builtins. Fixed by Lean-blaster#193 (`removeTypeAbbrev` hoisted over
         the whole of `generateUndeclaredFun`); repro in that repo's
         `Tests/FixedIssues/Issue36.lean`.
      2. `strLitSmt` emitted string literals unescaped, so a `ByteString` holding bytes
         outside printable ASCII produced a query Z3 rejects with `unexpected character`.
         Fixed by Lean-blaster#175; repro in `Tests/FixedIssues/Issue35.lean`.
    Note that a `#blaster` smoke test whose match branches agree is collapsed to `True`
    by the optimizer and never reaches translation, which is how `Tests/BlasterSmoke.lean`
    certified both capabilities for months without having either.
  * **FUEL.** `runSteps` maps exhaustion to `State.Error`, so it cannot distinguish
    rejection from running out of steps. Every property below is phrased with
    `erroredWithin`, which returns `false` on exhaustion, and is lifted to all fuels by
    `not_erroredWithinProgram_of_isSuccessful`. Those two — both in
    `PlutusCore/UPLC/CekMachine/Lemmas.lean` — are the only reason these statements are
    not bounded-model artifacts.
  * **LEDGER.** A raw `Data` context is not a ledger-valid context: nothing here enforces
    ordered value maps, canonical hash widths, resolved inputs matching out-refs, or
    redeemer/datum consistency, so contexts unreachable on chain are admitted. This cuts
    both ways. It only strengthens the gates, which say a *larger* set of contexts is
    rejected than the ledger could ever present. But it is exactly why
    `base_script_hash_unchecked` and `params_datum_tag_unchecked` are permissiveness
    observations rather than vulnerabilities: the shapes they exhibit are ones the ledger
    would never build. And each gate varies one field of a single fixed skeleton, so none
    of them quantifies over context *shape*.
  * **IDENTITY.** Nothing binds the executing artifact to the deployed script hash
    `a4da74e7cb6ea4f4e60456a0a6eabf0ccf83464ebe55664390ef39f8`; that the imported bytes
    are the deployed ones is an external assumption, checked only by `#guard_msgs` on
    the import and by the byte-offset provenance recorded in the loader.
  * **SMT.** `blaster` closes a valid goal with no proof term, so those theorems depend
    on `Blaster.Tactic.blasterProven`; their trust base is Blaster's optimizer, its
    Lean→SMT translation and Z3. `#print axioms` is emitted after each so the dependence
    is visible in the build log. (This axiom used to be plain `sorryAx`, which was
    indistinguishable from an ordinary hole; `warn.sorry` still governs the warning.)
    The `erroredWithin` lemmas in `PlutusCore/UPLC/CekMachine/Lemmas.lean` are by contrast
    fully kernel-checked, as are the three specialisations of them here. The one remaining
    `native_decide` use is `vk*_ok`, the nine decoding facts, which additionally trust the
    Lean compiler and the `Cryptograph` BLS implementation; every statement about the
    *artifact* now rests on Blaster and Z3 alone.
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Properties

open PlutusCore.ByteString
open PlutusCore.Data (Data)
open PlutusCore.Integer
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Term (Term)
open PlutusCore.UPLC.Utils (isSuccessful)
open PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2

/-! ## Observing the artifact

    `runSteps` conflates a genuine machine error with step-limit exhaustion, so no
    finite-fuel run distinguishes rejection from "not finished yet". `erroredWithin`
    separates the two, and `not_erroredWithinProgram_of_isSuccessful` lifts a bounded
    observation to every fuel. Both are generic to the CEK machine and live in
    `PlutusCore/UPLC/CekMachine/Lemmas.lean`; below are the two specialisations to this
    artifact that every property here is stated through. -/

/-- The artifact errors on `ctx` within `n` steps. -/
def reclaimErroredWithin (n : Nat) (ctx : Data) : Bool :=
  erroredWithinProgram n reclaimGlobalV2.script (ctxArgs ctx)

/-- The artifact accepts `ctx` at fuel `m`. -/
abbrev reclaimAccepts (m : Nat) (ctx : Data) : Prop :=
  isSuccessful (cekExecuteProgram reclaimGlobalV2.script (ctxArgs ctx) m)

/-- Acceptance at any fuel rules out an error observation at any prefix. This is what
    `atAnyFuel` and `never_accepted` are both built from, and the only route by which
    anything below escapes being a statement about `probeFuel` in particular. -/
theorem not_reclaimErroredWithin_of_accepts (n m : Nat) (ctx : Data) :
  reclaimAccepts m ctx
  --------------------
  → reclaimErroredWithin n ctx = false :=
    by
      intro h
      exact not_erroredWithinProgram_of_isSuccessful n m reclaimGlobalV2.script (ctxArgs ctx) h

/-! ## The scenario

    One concrete rewarding skeleton, faithful to what `reclaimGlobalValidatorV2Builtin`
    projects. Everything the validator does not read is left empty. The base script hash
    in the parameter datum is the deployed `ReclaimBase` hash. -/

/-- The `ReclaimBase` script hash named by the parameter datum in the live deployment. -/
def baseScriptHash : ByteString :=
  "\x74\x4c\xc4\x71\x8e\x81\x49\x20\x1c\x7e\x9c\xb3\xd3\xa5\x50\xf3\x4c\xb1\x8d\xfc\x80\x76\xa3\x31\x72\xd9\x35\x4d"

/-- The rewarding credential this script is invoked under. -/
def ownCred : Data := credScript "\x03"

/-- A parameter reference input carrying `qty` of `pol`/`tok` plus `datum`. -/
def refInput (pol tok : ByteString) (qty : Integer) (datum : Data) : Data :=
  mkTxInInfo (mkTxOutRef "\x01" 0)
    (mkTxOut (mkAddress (credScript "\x02")) [adaEntry 2000000, tokenEntry pol tok qty] datum)

/-- The datum a well-formed parameter output carries: inline, naming the base hash. -/
def goodParamsDatum : Data := inlineDatum (paramsDatum baseScriptHash)

/-- The well-formed parameter reference input: exactly one baked-policy `RECLAIMPARAMS`
    token and `goodParamsDatum`. -/
def goodRefInput : Data := refInput paramsPolicyId paramsTokenName 1 goodParamsDatum

/-- The context, parameterised on the values the gates inspect. -/
def ctxOf (purposeTag paramsIdx destStartIdx : Integer) (refs : List Data) : Data :=
  mkScriptContext (mkTxInfo [] refs [] [])
                  (reclaimRedeemer paramsIdx destStartIdx [] []) purposeTag ownCred

/-! Each gate varies exactly one field of an otherwise well-formed rewarding context, so
    each gets a one-argument specialisation of `ctxOf`. Reading a gate statement below,
    the only thing that is symbolic is the argument to one of these. -/

/-- Vary the script-purpose constructor index. -/
def ctxPurpose (purposeTag : Integer) : Data := ctxOf purposeTag 0 0 [goodRefInput]
/-- Vary the reference-input list. -/
def ctxRefs (refs : List Data) : Data := ctxOf 2 0 0 refs
/-- Vary the parameter reference index. -/
def ctxParamsIdx (paramsIdx : Integer) : Data := ctxOf 2 paramsIdx 0 [goodRefInput]
/-- Vary the destination-output start index. -/
def ctxDestStart (destStartIdx : Integer) : Data := ctxOf 2 0 destStartIdx [goodRefInput]
/-- Vary the parameter output's policy id, token name, quantity and datum. -/
def ctxParams (pol tok : ByteString) (qty : Integer) (datum : Data) : Data :=
  ctxOf 2 0 0 [refInput pol tok qty datum]

/-- The fully well-formed context: `ctxParams` at every good value. Equal to
    `ctxPurpose 2` and to `ctxRefs [goodRefInput]`. -/
def ctxGood : Data := ctxParams paramsPolicyId paramsTokenName 1 goodParamsDatum

/-- Fuel for the gate theorems: above every gate (the last fires at 1383) and below the
    step at which a fully well-formed parameter section errors (1674), so every gate
    premise below is satisfiable — see `good_params_not_yet_errored`. -/
abbrev probeFuel : Nat := 1390

/-- Lift a `probeFuel` gate to a statement about acceptance at *any* fuel. Every
    `success_requires_*` theorem below is one application of this, so the fuel-monotonicity
    argument appears exactly once. -/
theorem atAnyFuel {P : Prop} {ctx : Data} (m : Nat) :
  (reclaimErroredWithin probeFuel ctx = false → P) →
  reclaimAccepts m ctx
  ----------------------------------------------------
  → P :=
    by
      intros gate h
      exact gate (not_reclaimErroredWithin_of_accepts probeFuel m ctx h)

/-! ## Why the properties are not phrased with `isSuccessful`

    `#prep_uplc` is the natural vehicle, and it is used here — but acceptance requires a
    genuine Groth16 proof, and the pairing builtins are opaque to the optimizer, so the
    prepared residual can never halt. The theorem below proves that, which is precisely
    what makes every `isSuccessful → P` statement about this artifact vacuous. -/

def purposeArgs (purposeTag : Integer) : List Term := ctxArgs (ctxPurpose purposeTag)

-- 1700 rather than `probeFuel`: `#prep_uplc` needs a literal, and here the fuel wants to
-- be *above* 1674, so that even the well-formed context has genuinely errored and
-- `prepared_never_halts` is not an artifact of exhaustion.
#prep_uplc preparedPurpose reclaimGlobalV2 purposeArgs 1700

set_option warn.sorry false in
/-- The prepared residual never halts, whatever the script purpose. Stated so that the
    vacuity is a machine-checked fact rather than a claim in a comment: an
    `isSuccessful (preparedPurpose.prop _) → P` theorem would hold for *any* `P`. -/
theorem prepared_never_halts (purposeTag : Integer) :
  ¬ isSuccessful (preparedPurpose.prop purposeTag) := by blaster

/-! ## The purpose gate

    First of the eight, and the only one whose value the validator reads *before*
    `validateGlobal`'s strict bindings — which is why it is also the only one that
    resolves before the first `uncompress` at step 489. -/

set_option warn.sorry false in
/-- Any script-purpose constructor index other than 2 (`RewardingScript`) makes the
    artifact error within `probeFuel` steps. -/
theorem purpose_gate (purposeTag : Integer) :
  reclaimErroredWithin probeFuel (ctxPurpose purposeTag) = false
  --------------------------------------------------------------
  → purposeTag = 2 := by blaster

/-- **The artifact is a rewarding script and only a rewarding script.** If it accepts a
    context of this shape at *any* fuel, the script-purpose constructor index is 2.

    This is the artifact-level counterpart of the premise `OwnershipVerifyExample` leaves
    entirely unmodelled — that the code being reasoned about is the reclaim script,
    invoked as a withdrawal. -/
theorem success_requires_rewarding_purpose (m : Nat) (purposeTag : Integer) :
  reclaimAccepts m (ctxPurpose purposeTag)
  ----------------------------------------
  → purposeTag = 2 :=
    by
     intro h
     exact atAnyFuel m (purpose_gate purposeTag) h

/-! ## The remaining seven gates

    Same shape as `purpose_gate` throughout: one symbolic hole, an `erroredWithin`
    premise, no other hypotheses. All seven execute `uncompress` on the way to their
    verdict and translate regardless, because the verdict does not depend on how the key
    decodes — see **REACH**.

    That any of these are reachable with a symbolic hole is recent: before
    Lean-blaster#193 a hole whose value flowed into `validateGlobal` aborted in
    `createPredQualifierAppAux`, and these seven facts existed only as concrete
    witnesses over fixed contexts. -/

/-- What `decodeValidatedParams` actually demands of the parameter output's datum field:
    a `Constr` with at least one field, whose first field is a `Constr` with at least one
    field, whose first field is a `B`. Neither constructor tag is ever inspected — see
    `params_datum_tag_unchecked`. -/
def paramsDatumShapeOk : Data → Bool
  | .Constr _ (.Constr _ (.B _ :: _) :: _) => true
  | _ => false

section Gates
set_option warn.sorry false

/-- The transaction must carry at least one reference input. -/
theorem ref_inputs_gate (refs : List Data) :
  reclaimErroredWithin probeFuel (ctxRefs refs) = false
  -----------------------------------------------------
  → refs ≠ [] := by blaster

/-- The parameter reference index must select an actual reference input; with one
    present, it must be 0. Negative indices are rejected rather than wrapping. -/
theorem params_idx_gate (paramsIdx : Integer) :
  reclaimErroredWithin probeFuel (ctxParamsIdx paramsIdx) = false
  ---------------------------------------------------------------
  → paramsIdx = 0 := by blaster

/-- The destination-output start index must not run past the output list; with no
    outputs, it must be 0. -/
theorem dest_start_gate (destStartIdx : Integer) :
  reclaimErroredWithin probeFuel (ctxDestStart destStartIdx) = false
  ------------------------------------------------------------------
  → destStartIdx = 0 := by blaster

/-- **Parameter-NFT authentication, 1/4:** the NFT must sit under the baked policy id.
    Over *every* `ByteString`, so it cannot be forged under any other policy. -/
theorem params_policy_gate (pol : ByteString) :
  reclaimErroredWithin probeFuel (ctxParams pol paramsTokenName 1 goodParamsDatum) = false
  ----------------------------------------------------------------------------------------
  → pol = paramsPolicyId := by blaster

/-- **Parameter-NFT authentication, 2/4:** the NFT must carry the baked token name.
    Again over every `ByteString`. -/
theorem params_token_gate (tok : ByteString) :
  reclaimErroredWithin probeFuel (ctxParams paramsPolicyId tok 1 goodParamsDatum) = false
  ----------------------------------------------------------------------------------------
  → tok = paramsTokenName := by blaster

/-- **Parameter-NFT authentication, 3/4:** the quantity must be exactly one — the check
    is "exactly one", not "at least one", so the output cannot be a mixed bag. -/
theorem params_qty_gate (qty : Integer) :
  reclaimErroredWithin probeFuel (ctxParams paramsPolicyId paramsTokenName qty goodParamsDatum) = false
  -----------------------------------------------------------------------------------------------------
  → qty = 1 := by blaster

/-- **Parameter-NFT authentication, 4/4:** the datum must have the nested shape
    `decodeValidatedParams` walks. That rules out a missing datum (`Constr 0 []` has no
    first field) and a datum hash (`Constr 1 [B _]`, whose first field is a `B` rather
    than a `Constr`). Over every `Data`. -/
theorem params_datum_gate (d : Data) :
  reclaimErroredWithin probeFuel (ctxParams paramsPolicyId paramsTokenName 1 d) = false
  -------------------------------------------------------------------------------------
  → paramsDatumShapeOk d = true := by blaster

end Gates

/-! ### The same seven, lifted to every fuel

    Each is one `atAnyFuel` application, exactly as `success_requires_rewarding_purpose`
    is built from `purpose_gate`. None mentions `probeFuel`. -/

/-- Acceptance requires a reference input to have been provided. -/
theorem success_requires_reference_input (m : Nat) (refs : List Data) :
  reclaimAccepts m (ctxRefs refs)
  -------------------------------
  → refs ≠ [] :=
    by
      intro h
      exact atAnyFuel m (ref_inputs_gate refs) h

/-- Acceptance requires the parameter reference index to be in range. -/
theorem success_requires_params_idx_in_range (m : Nat) (paramsIdx : Integer) :
  reclaimAccepts m (ctxParamsIdx paramsIdx)
  -----------------------------------------
  → paramsIdx = 0 :=
    by
      intro h
      exact atAnyFuel m (params_idx_gate paramsIdx) h

/-- Acceptance requires the destination-output start index to be in range. -/
theorem success_requires_dest_start_in_range (m : Nat) (destStartIdx : Integer) :
  reclaimAccepts m (ctxDestStart destStartIdx)
  --------------------------------------------
  → destStartIdx = 0 :=
    by
      intro h
      exact atAnyFuel m (dest_start_gate destStartIdx) h

/-- **The parameter NFT cannot be forged under another policy, at any fuel.** -/
theorem success_requires_baked_policy (m : Nat) (pol : ByteString) :
  reclaimAccepts m (ctxParams pol paramsTokenName 1 goodParamsDatum)
  ------------------------------------------------------------------
  → pol = paramsPolicyId :=
    by
      intro h
      exact atAnyFuel m (params_policy_gate pol) h

/-- **The parameter NFT must carry the baked token name, at any fuel.** -/
theorem success_requires_baked_token_name (m : Nat) (tok : ByteString) :
  reclaimAccepts m (ctxParams paramsPolicyId tok 1 goodParamsDatum)
  -----------------------------------------------------------------
  → tok = paramsTokenName :=
    by
      intro h
      exact atAnyFuel m (params_token_gate tok) h

/-- **The parameter NFT must be unique, at any fuel.** -/
theorem success_requires_single_params_nft (m : Nat) (qty : Integer) :
  reclaimAccepts m (ctxParams paramsPolicyId paramsTokenName qty goodParamsDatum)
  -------------------------------------------------------------------------------
  → qty = 1 :=
    by
      intro h
      exact atAnyFuel m (params_qty_gate qty) h

/-- **The parameters must be inline and well-shaped, at any fuel.** -/
theorem success_requires_params_datum_shape (m : Nat) (d : Data) :
  reclaimAccepts m (ctxParams paramsPolicyId paramsTokenName 1 d)
  ---------------------------------------------------------------
  → paramsDatumShapeOk d = true :=
    by
      intro h
      exact atAnyFuel m (params_datum_gate d) h

/-! ## The verifying key the good path decodes

    Past the parameter gates the artifact starts unpacking its baked 672-byte verifying
    key: `bls12_381_G1_uncompress` first fires at CEK step 489, and by `probeFuel` nine
    compressed points — four G1, five G2 — have been decoded. `parseVerifyingKeyBatch`
    reads them in the interleaved order α, β, γ, δ, IC₀, IC₁, K₂, ckG, ckGSN, whereas the
    literals below are grouped by group, so the two orders differ; each `def` names the
    component it holds.

    These nine slices are exactly the nine points of `OwnershipVerifyExample.ParsedVK`,
    hence the nine conjuncts of its `vkInSubgroup` — the one seam between the two files:

    | VK offset | width | here     | `ParsedVK` field |
    |----------:|------:|----------|------------------|
    |         0 |    48 | `vkG1_0` | `alpha`          |
    |        48 |    96 | `vkG2_0` | `beta`           |
    |       144 |    96 | `vkG2_1` | `gamma`          |
    |       240 |    96 | `vkG2_2` | `delta`          |
    |       336 |    48 | `vkG1_1` | `ic0`            |
    |       384 |    48 | `vkG1_2` | `ic1`            |
    |       432 |    48 | `vkG1_3` | `k2`             |
    |       480 |    96 | `vkG2_3` | `ckG`            |
    |       576 |    96 | `vkG2_4` | `ckGSN`          |

    That map is verified by reassembling the key from the artifact: the flat encoding
    stores it as length-prefixed chunks of 255/255/162 bytes (offsets 2644, 2900, 3156 in
    the CBOR, `0x00` terminator at 3318), and all nine literals match their offsets in
    the concatenation. Seven also occur verbatim in the `.cbor.hex`; the two that do not
    are `delta` and `ckG`, which are precisely the two that straddle a chunk boundary.

    Both builtins are Lean `opaque`, so the optimizer cannot reduce them even here,
    where every argument is a closed literal. What survives to the solver is therefore
    an `ite` chain testing `is-Except.ok` on nine applications of an *uninterpreted*
    function, which Z3 can only falsify: it is free to answer `.error` for any of them.
    That, and not any symbolic hole, is what stops `blaster` on the good path.

    Getting a slice wrong cannot make anything below unsound — a mismatched literal
    simply fails to line up with the residual and the goal comes back `Falsified`. -/

/-- `ParsedVK.alpha` — VK offset 0. -/
def vkG1_0 : ByteString :=
  "\x8b\xa1\x52\x53\x48\x61\xef\x6f\x4e\x0f\x90\x7b\x36\x7e\x69\x44\x94\x7c\x03\xc9\xf2\xef\x6e\xc4\xdd\xdc\x6f\xa3\x12\x52\x78\xab\xf1\x37\xac\xae\x66\xaa\x16\x7e\x0b\x9e\x52\x3d\x12\x37\xdc\x95"
/-- `ParsedVK.ic0` — VK offset 336. -/
def vkG1_1 : ByteString :=
  "\xac\x07\x9f\xf2\xb7\x71\x77\x8a\x2d\x60\x89\xcc\xbd\x34\x57\x79\xf3\x0f\x9e\xf7\x94\xdb\x3d\x27\x46\x44\xb8\x53\xc1\x0d\xac\xc3\x78\xbb\x71\x8b\x93\xd3\xe2\x7f\x47\x18\x0f\x85\x4e\x0a\x40\x38"
/-- `ParsedVK.ic1` — VK offset 384. The basis point of the single public input; the
    model's `IsHonestSetup` additionally requires it to be non-zero, which nothing here
    establishes. -/
def vkG1_2 : ByteString :=
  "\xb6\x52\x7a\xd1\x74\xec\x36\x11\x6e\x4b\x74\x9f\xf4\x4d\x22\xf3\xd8\x2d\x42\xd7\x42\xa4\x64\xaf\x8f\x35\x43\x00\x7a\x9f\xd8\x24\xde\x55\xfa\x16\xae\x04\xdc\x7c\xe7\x6f\xc8\x84\x98\xf4\x1d\x32"
/-- `ParsedVK.k2` — VK offset 432. -/
def vkG1_3 : ByteString :=
  "\xa8\x20\x7d\x61\x81\x7f\xbc\x5f\x58\xb3\x36\xc4\xf5\x6c\x3d\x47\x16\xdc\x1f\x1a\xb8\x41\x5f\xac\xd0\xc3\x9a\x2b\x4e\xb9\x73\x82\xe3\xc7\x6f\x67\x57\x53\x4e\x3f\xa0\xf0\x74\x19\x04\x04\xf0\x8a"

/-- `ParsedVK.beta` — VK offset 48. -/
def vkG2_0 : ByteString :=
  "\xa0\xf9\xdb\x65\xc7\x0c\x3e\x24\xbe\x4c\xa2\x91\x3b\x66\x68\xf6\x7e\x85\xb8\x89\x61\x7d\x4f\x02\xf1\x0e\x77\x4a\x99\x7f\x25\xef\xaf\xf3\x71\xae\xb0\x49\x6b\x4f\x18\xfb\xa5\x69\x10\xb1\x5d\xb3\x00\x69\xb9\x80\xeb\x78\x4e\xf9\xfa\xbd\x71\xaa\xdc\x03\x4e\x82\x63\xbf\x7b\x7f\xd6\x9b\x44\x28\xcd\x40\xaa\xb3\x91\x17\xe7\x96\xed\x0e\x45\xe5\x72\x9c\x1e\x65\x85\x82\x3b\xe3\xbc\x0c\xb8\xf8"
/-- `ParsedVK.gamma` — VK offset 144. The model's `IsHonestSetup` additionally requires
    it to be non-zero, which nothing here establishes. -/
def vkG2_1 : ByteString :=
  "\xb6\x8b\xfc\x80\xc1\x7d\xce\xac\x39\x88\xe9\x7e\x91\xb1\xb7\x94\x84\x96\x76\x09\x32\xca\x7f\x0d\xf6\x16\xf4\xa3\x49\xce\x32\xff\xf3\xd8\x7c\x1e\x87\x53\x5f\xd1\x71\x21\x90\x06\x94\xdc\x6a\x8e\x16\x42\xf3\x08\xbc\x90\xbd\xb4\xde\x02\x68\x3f\x8d\x65\xc1\x81\xdf\x83\x6d\x5b\xc5\x37\x8f\xe8\x61\x2e\x8e\x78\x83\xf5\x14\xb8\xb4\x2b\xd7\xd5\xd4\xc9\x19\x20\x60\x69\x2e\x48\x19\x8d\x6b\x09"
/-- `ParsedVK.delta` — VK offset 240. Straddles the 255-byte flat chunk boundary, so it
    does not occur contiguously in the `.cbor.hex`. -/
def vkG2_2 : ByteString :=
  "\x80\xef\x6d\xed\xf6\x3c\x31\x05\xe3\x97\x6e\xac\xbd\x7c\xfe\xcc\x90\x42\xfb\x5f\x90\xb0\x29\xde\x92\x06\x3c\x37\xcd\x3e\x17\x12\xbd\xf7\xb1\x65\x57\x7f\x40\xd2\x11\xe9\x1d\x76\xd9\xb5\x41\x58\x09\x22\xb7\x7f\x2c\x82\x06\x56\xd0\x62\x43\x83\xc6\xf5\xf8\x70\xd9\xc7\x33\x04\x85\xc3\xe2\x26\x10\x28\x17\xc3\xf0\x6f\x1f\xf7\xc2\x42\x7f\xf0\x33\x1b\xb1\x17\xc0\xa8\xa9\x9a\x56\x56\xf0\x14"
/-- `ParsedVK.ckG` — VK offset 480, the BSB22 commitment key. Straddles the second flat
    chunk boundary at 510, so it does not occur contiguously in the `.cbor.hex`. -/
def vkG2_3 : ByteString :=
  "\x84\xf6\x75\xb2\xfb\x70\x06\xae\x33\xf1\x52\xae\x89\x17\x89\xe9\x20\x47\x13\xbd\x75\x70\xe0\xe8\x2c\xd2\xea\x0a\xa6\x90\x20\x0a\x1f\x42\x8b\x70\x3f\xa1\x70\xf4\x17\xbb\x29\x06\x4d\x2d\x5c\xc2\x0c\x98\x9c\x22\xa2\x38\x45\x62\xdf\xb8\xbd\x08\x5e\xa3\x2a\x2c\x66\x90\xb1\x62\x2b\xa1\x72\x37\xa7\xe5\x8a\xd9\xd1\x41\x12\xa6\xb6\x00\x2b\x04\xd5\xcd\xb2\xea\x64\x28\x13\x99\x26\x0c\x8d\xe2"
/-- `ParsedVK.ckGSN` — VK offset 576, the commitment key times `-σ` (the PoK companion). -/
def vkG2_4 : ByteString :=
  "\x86\xda\xe8\x97\xb5\x5e\xa1\x2c\x5e\x5c\x12\xd2\x35\x7e\xdd\xe9\x34\x07\x28\xca\x9c\x44\x11\x34\xe4\x01\x18\xeb\x88\xb2\x8a\xa5\x88\x55\x8e\xe2\x9c\x29\xf5\x2a\x7c\x73\xe1\x3b\x11\x6d\x35\xf6\x17\x2e\x2d\xb3\x5e\xc9\x12\xad\x9f\x3a\xfc\xbc\x0c\xc2\x5c\x78\xb3\xac\x12\x31\x7d\xb3\xd7\x54\x2f\x79\x5b\x68\xbe\x03\x11\xd6\xd2\x19\x0f\x86\xdd\x6a\xdf\xc5\xf9\x3f\x28\xea\x48\x6b\x8a\xb9"

open PlutusCore.Crypto.BLS12_381.G1.Internal (bls12_381_G1_uncompress)
open PlutusCore.Crypto.BLS12_381.G2.Internal (bls12_381_G2_uncompress)

/-! Each decoding fact is a ground statement about one 48- or 96-byte constant, decided
    by the `Cryptograph` implementation. These are the CURVE-class premises — and the
    only ones — that the artifact-level proof below needs.

    They are also the artifact-level counterpart of `OwnershipVerifyExample.vkInSubgroup`,
    whose comment says of its nine conjuncts that "on chain this is not an assumption but
    a consequence: each point is produced by `uncompress`". These nine theorems are that
    consequence, for this key: `isOk` says the point exists, and
    `g1_uncompress_subgroup` / `g2_uncompress_subgroup` promote existence to order-r
    subgroup membership. The remaining parts of `IsHonestSetup` — `IsHonestSetupCore`,
    `gamma ≠ 0`, `ic1 ≠ 0` — have no counterpart and stay assumptions. -/

theorem vkG1_0_ok : (bls12_381_G1_uncompress vkG1_0).isOk = true := by native_decide
theorem vkG1_1_ok : (bls12_381_G1_uncompress vkG1_1).isOk = true := by native_decide
theorem vkG1_2_ok : (bls12_381_G1_uncompress vkG1_2).isOk = true := by native_decide
theorem vkG1_3_ok : (bls12_381_G1_uncompress vkG1_3).isOk = true := by native_decide

theorem vkG2_0_ok : (bls12_381_G2_uncompress vkG2_0).isOk = true := by native_decide
theorem vkG2_1_ok : (bls12_381_G2_uncompress vkG2_1).isOk = true := by native_decide
theorem vkG2_2_ok : (bls12_381_G2_uncompress vkG2_2).isOk = true := by native_decide
theorem vkG2_3_ok : (bls12_381_G2_uncompress vkG2_3).isOk = true := by native_decide
theorem vkG2_4_ok : (bls12_381_G2_uncompress vkG2_4).isOk = true := by native_decide

/-- The nine bundled into one premise, so the theorems below take `VkDecodes` rather than
    nine separate hypotheses. The optimizer unfolds it back into the conjunction. -/
def VkDecodes : Prop :=
  (bls12_381_G1_uncompress vkG1_0).isOk = true ∧
  (bls12_381_G1_uncompress vkG1_1).isOk = true ∧
  (bls12_381_G1_uncompress vkG1_2).isOk = true ∧
  (bls12_381_G1_uncompress vkG1_3).isOk = true ∧
  (bls12_381_G2_uncompress vkG2_0).isOk = true ∧
  (bls12_381_G2_uncompress vkG2_1).isOk = true ∧
  (bls12_381_G2_uncompress vkG2_2).isOk = true ∧
  (bls12_381_G2_uncompress vkG2_3).isOk = true ∧
  (bls12_381_G2_uncompress vkG2_4).isOk = true

theorem vkDecodes : VkDecodes :=
  ⟨vkG1_0_ok, vkG1_1_ok, vkG1_2_ok, vkG1_3_ok, vkG2_0_ok, vkG2_1_ok, vkG2_2_ok, vkG2_3_ok, vkG2_4_ok⟩

/-! ## The good path, and two things the artifact does not check

    Three statements of the form "the machine has *not* errored by `probeFuel`". These are
    the only properties here that depend on the verifying key decoding: Z3 may answer
    `.error` for an uninterpreted `uncompress`, so each takes `VkDecodes` as a premise and
    is discharged with `vkDecodes` immediately afterwards. Everything else about the 1390
    steps — the gates, the slicing, the control flow — is still Z3's work; dropping the
    premise makes each `Falsified`, so it is not idle.

    The latter two record where the artifact is more permissive than the types it reads.
    Neither is exploitable on chain and both belong under **LEDGER**: a real transaction
    cannot present these shapes, because the ledger builds the reference output and its
    `OutputDatum`. They are worth stating because the invariant being relied on is
    someone else's. -/

/-- A base script hash that is *not* the deployed one. -/
def wrongBaseScriptHash : ByteString :=
  "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"

/-- A datum whose outer tag is 1 — `OutputDatumHash`, which the ledger would only ever
    build with a `B` payload — carrying a `Constr` payload instead. -/
def tagMismatchedParamsDatum : Data := .Constr 1 [paramsDatum baseScriptHash]

section GoodPath
set_option warn.sorry false

/-- Non-vacuity anchor: on a well-formed parameter section the artifact has *not* errored
    by `probeFuel`, so every gate premise above is satisfiable.

    In particular it anchors `purpose_gate`: `ctxGood` is definitionally `ctxPurpose 2`,
    so this says exactly that at tag 2 the machine has not errored yet. Without it that
    theorem would be an implication from an empty hypothesis. -/
theorem good_params_not_yet_errored_of (h : VkDecodes) :
  reclaimErroredWithin probeFuel ctxGood = false := by blaster

/-- The base script hash in the parameter datum is read by `unsafeDataAsB` and never
    checked against anything, so any byte string passes — here a hash that is not the
    deployed one. Found by `params_datum_gate`'s analogue for the hash coming back
    *falsifiable*: `→ bh = baseScriptHash` yields a counterexample.

    The hash decides which inputs count as reclaim inputs, so authority over it rests
    entirely on the parameter NFT being unforgeable (`params_policy_gate`,
    `params_token_gate`, `params_qty_gate`) and not on any check of the value. -/
theorem base_script_hash_unchecked_of (h : VkDecodes) :
  reclaimErroredWithin probeFuel
    (ctxParams paramsPolicyId paramsTokenName 1
      (inlineDatum (paramsDatum wrongBaseScriptHash))) = false := by blaster

/-- Neither constructor tag in the datum chain is inspected, so a mismatched
    `OutputDatum` tag sails through. `params_datum_gate` says exactly what is required,
    and it mentions no tag. -/
theorem params_datum_tag_unchecked_of (h : VkDecodes) :
  reclaimErroredWithin probeFuel
    (ctxParams paramsPolicyId paramsTokenName 1 tagMismatchedParamsDatum) = false := by blaster

end GoodPath

/-! The same three, with `VkDecodes` discharged. -/

theorem good_params_not_yet_errored :
  reclaimErroredWithin probeFuel ctxGood = false := good_params_not_yet_errored_of vkDecodes

theorem base_script_hash_unchecked :
  reclaimErroredWithin probeFuel
    (ctxParams paramsPolicyId paramsTokenName 1
      (inlineDatum (paramsDatum wrongBaseScriptHash))) = false := base_script_hash_unchecked_of vkDecodes

theorem params_datum_tag_unchecked :
  reclaimErroredWithin probeFuel
    (ctxParams paramsPolicyId paramsTokenName 1 tagMismatchedParamsDatum) = false := params_datum_tag_unchecked_of vkDecodes

/-! ## Lifting an error observation to every fuel -/

/-- A context the artifact errors on within `probeFuel` steps is never accepted, at any
    fuel.

    Nothing in this module uses it: every property here is an implication, so it goes
    through `atAnyFuel` instead. This is the form to reach for when starting from a
    *concrete* rejection — a specific context shown to error — which is how the gates
    above were stated before they were generalised. -/
theorem never_accepted (m : Nat) (ctx : Data) :
  reclaimErroredWithin probeFuel ctx = true
  -----------------------------------------
  → ¬ reclaimAccepts m ctx :=
    by
      intro herr
      exact not_isSuccessful_of_erroredWithinProgram probeFuel m reclaimGlobalV2.script (ctxArgs ctx) herr

end PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2Properties
