import PlutusCore.UPLC

/-
  The compiled `reclaim-global-v2` artifact, plus raw-`Data` encoders for the Plutus V3
  script context it consumes.

  The artifact is the locked Preprod deployment of `Ownership.ReclaimGlobalV2`
  (script hash `a4da74e7cb6ea4f4e60456a0a6eabf0ccf83464ebe55664390ef39f8`), a
  **rewarding** (withdrawal) script. Source of truth for every shape below:
  `.proof-tool/contracts/ownership-verifier/src/Ownership/ReclaimGlobalV2.hs`.

  Why raw `Data` and not typed `CardanoLedgerApi` structures: that library is not a
  dependency of this package and cannot become one — `CardanoLedgerApiBlaster` itself
  requires `PlutusCore`, so the edge would close a cycle. Encoding by hand is also the
  cheaper option for `#prep_uplc`: symbolic *breadth* rather than fuel is what drives
  the optimizer's cost, and a mostly-concrete skeleton with a handful of named holes is
  far smaller than a fully symbolic typed context.

  The validator reads the context positionally via `unsafeDataAsConstr`/`BI.head`/
  `BI.tail`, never by constructor tag (except for the purpose gate), so the encoders
  below only have to agree with the ledger on *field order*. Field orders are taken
  from `.cardano-ledger-api/CardanoLedgerApi/V3/Contexts.lean`; the V3-specific traps
  worth restating are that `txInfoId` is a bare `B` (V1/V2 wrap it in `Constr 0`),
  withdrawals are keyed by `Credential` rather than `StakingCredential`, `txInfoMint`
  carries no Ada entry, and the treasury fields are `Option Integer` at `Data` level.
-/

namespace PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2

open PlutusCore.ByteString
open PlutusCore.Data (Data)
open PlutusCore.Integer
open PlutusCore.UPLC.Term (Term Const)

/-! ## Parameters baked into this artifact

    Applied by `export/ReclaimDeploymentScripts.hs` in `global-v2` mode and recovered
    from the compiled bytes; each occurs exactly once in the artifact, at the byte
    offset noted. `ByteString` is a one-byte-per-`Char` wrapper over `String`, so these
    are written with `\xNN` escapes. -/

/-- `paramsCurrencySymbol`, the policy id of the parameter NFT (28 bytes, offset 2595). -/
def paramsPolicyId : ByteString :=
  "\xd6\x77\x7b\x8c\x3b\xe1\xc6\xc0\xc9\xba\xba\x52\xa8\x80\xc1\x98\x0a\x66\x2c\x16\xff\xc0\x88\x5e\xca\xa0\x31\x19"

/-- `paramsTokenName`, the parameter NFT's token name (offset 2627). -/
def paramsTokenName : ByteString := "RECLAIMPARAMS"

/-- `verifierKeyHash`, the BLAKE2b-256 hash of the 672-byte verifying key
    (32 bytes, offset 3322). The key itself is baked in as a chunked flat bytestring
    at offset 2643 and is never re-hashed on chain. -/
def verifierKeyHash : ByteString :=
  "\x06\xce\x91\x3c\x93\x1a\x53\x56\x1f\xe5\xd0\x22\xed\x45\xa5\xfb\xc0\x33\xb0\x6d\x80\xee\xbd\xd9\xf6\x46\xd2\x3a\x05\xb7\xd5\xc4"

/-! ## Credentials, addresses, values -/

/-- `Credential.ScriptCredential h`. -/
def credScript (h : ByteString) : Data := .Constr 1 [.B h]
/-- `Credential.PubKeyCredential h`. -/
def credPubKey (h : ByteString) : Data := .Constr 0 [.B h]
/-- `Address` with no staking credential. -/
def mkAddress (cred : Data) : Data := .Constr 0 [cred, .Constr 1 []]

/-- A lovelace entry in a `Value`: policy `""`, token `""`. -/
def adaEntry (n : Integer) : Data × Data := (.B "", .Map [(.B "", .I n)])
/-- A single-asset entry in a `Value`. -/
def tokenEntry (pol tok : ByteString) (n : Integer) : Data × Data := (.B pol, .Map [(.B tok, .I n)])

/-! ## Output datums

    `decodeValidatedParams` reads the parameter output's datum with
    `BI.head (BI.snd (unsafeDataAsConstr outputDatum))`, i.e. it takes the first field of
    whatever constructor it finds. That is `Constr 2 [d]` for an inline datum, so the
    inline case yields `d`; `NoOutputDatum` is `Constr 0 []` and makes `BI.head` fail. -/

/-- `OutputDatum.NoOutputDatum`. -/
def noDatum : Data := .Constr 0 []
/-- `OutputDatum.OutputDatumHash h`. -/
def datumHash (h : ByteString) : Data := .Constr 1 [.B h]
/-- `OutputDatum.OutputDatum d` — an inline datum. -/
def inlineDatum (d : Data) : Data := .Constr 2 [d]

/-! ## Transaction pieces -/

/-- `TxOut`: address, value, datum, optional reference script. -/
def mkTxOut (addr : Data) (value : List (Data × Data)) (datum : Data) : Data :=
  .Constr 0 [addr, .Map value, datum, .Constr 1 []]

/-- `TxOutRef`: V3 keeps the transaction id as a bare `B`. -/
def mkTxOutRef (tid : ByteString) (idx : Integer) : Data := .Constr 0 [.B tid, .I idx]

/-- `TxInInfo`: the out-ref plus its resolved output. `txInResolved` is field 1. -/
def mkTxInInfo (ref out : Data) : Data := .Constr 0 [ref, out]

/-- The parameter-holder datum: a constructor whose first field is the base
    `ReclaimBase` script hash. Built by `reclaimGlobalParamsData`. -/
def paramsDatum (baseScriptHash : ByteString) : Data := .Constr 0 [.B baseScriptHash]

/-- The `ReclaimBase` datum: a constructor whose first field is the 28-byte payment
    key hash being reclaimed. -/
def baseDatum (paymentKeyHash : ByteString) : Data := .Constr 0 [.B paymentKeyHash]

/-- `(-inf, +inf)`, both bounds closed. The validator never reads the validity range;
    this is here so the encoded context stays well-formed. -/
def alwaysValidRange : Data :=
  .Constr 0 [ .Constr 0 [.Constr 0 [], .Constr 1 []]
            , .Constr 0 [.Constr 2 [], .Constr 1 []] ]

/-- A V3 `TxInfo`. All sixteen fields in ledger order; everything the validator does
    not read is left empty or `none`. Only fields 0-2 (inputs, reference inputs,
    outputs) and — for a self-consistent rewarding context — field 6 (withdrawals) are
    meaningful here. -/
def mkTxInfo (inputs refInputs outputs : List Data) (wdrl : List (Data × Data)) : Data :=
  .Constr 0
    [ .List inputs              -- 0  txInfoInputs
    , .List refInputs           -- 1  txInfoReferenceInputs
    , .List outputs             -- 2  txInfoOutputs
    , .I 0                      -- 3  txInfoFee
    , .Map []                   -- 4  txInfoMint          (V3: no Ada entry)
    , .List []                  -- 5  txInfoTxCerts
    , .Map wdrl                 -- 6  txInfoWdrl          (keyed by Credential)
    , alwaysValidRange          -- 7  txInfoValidRange
    , .List []                  -- 8  txInfoSignatories
    , .Map []                   -- 9  txInfoRedeemers
    , .Map []                   -- 10 txInfoData
    , .B ""                     -- 11 txInfoId            (V3: bare B)
    , .Map []                   -- 12 txInfoVotes
    , .List []                  -- 13 txInfoProposalProcedures
    , .Constr 1 []              -- 14 txInfoCurrentTreasuryAmount = none
    , .Constr 1 []              -- 15 txInfoTreasuryDonation      = none
    ]

/-- The redeemer, `reclaimGlobalRedeemerDataV2`: the parameter reference-input index,
    the number of outputs to drop before the destination suffix, the 336-byte proofs,
    and the 32-byte claimed statement digests. -/
def reclaimRedeemer (paramsIdx destStartIdx : Integer) (proofs digests : List Data) : Data :=
  .Constr 0 [.I paramsIdx, .I destStartIdx, .List proofs, .List digests]

/-- A `ScriptContext`. `purposeTag` is the `ScriptInfo` constructor index and is left a
    parameter so the purpose gate itself can be stated as a property: the validator
    accepts only tag 2 (`RewardingScript`), and `constrTag scriptInfo` is the very first
    thing it compares. -/
def mkScriptContext (txInfo redeemer : Data) (purposeTag : Integer) (cred : Data) : Data :=
  .Constr 0 [txInfo, redeemer, .Constr purposeTag [cred]]

/-- The single argument a Plutus V3 rewarding script receives. -/
def ctxArgs (ctx : Data) : List Term := [Term.Const (Const.Data ctx)]

/-! ## The artifact

    `#guard_msgs` pins the decoder's own report, so a change of path or encoding fails
    the build rather than silently importing something else. Note that Lake does not
    track this hex file as a module dependency: after editing it, delete this module's
    `.olean` or the stale one is reused. -/

/-- info: Successfully decoded single CBOR hex 'PlutusCore/Crypto/BLS12_381/Tests/reclaim-global-v2.cbor.hex' -/
#guard_msgs in
#import_uplc reclaimGlobalV2 PlutusV3 single_cbor_hex
  "PlutusCore/Crypto/BLS12_381/Tests/reclaim-global-v2.cbor.hex"

end PlutusCore.Crypto.BLS12_381.Tests.ReclaimGlobalV2
