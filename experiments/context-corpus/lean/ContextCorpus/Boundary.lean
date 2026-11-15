import PlutusCore.UPLC.Term
import ContextCorpus.Representation

namespace ContextCorpus
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term)

/-- An outer-shape view, not a ledger-validity definition. Every field stays
    universally quantified; nested elements remain raw Data. There is no list
    length bound or fixed value for another transaction field. -/
structure View where
  inputs : List Data
  referenceInputs : List Data
  outputs : List Data
  fee : Int
  mint : List (Data × Data)
  certificates : List Data
  withdrawals : List (Data × Data)
  validityRange : Data
  signatories : List Data
  redeemers : List (Data × Data)
  datums : List (Data × Data)
  transactionId : ByteString
  votes : List (Data × Data)
  proposals : List Data
  currentTreasury : Data
  donation : Data
  redeemer : Data
  info : Data

def encode (v : View) : Data :=
  .Constr 0 [.Constr 0 [.List v.inputs, .List v.referenceInputs, .List v.outputs,
    .I v.fee, .Map v.mint, .List v.certificates, .Map v.withdrawals, v.validityRange,
    .List v.signatories, .Map v.redeemers, .Map v.datums, .B v.transactionId,
    .Map v.votes, .List v.proposals, v.currentTreasury, v.donation], v.redeemer, v.info]

def decode : Data → Option View
  | .Constr 0 [.Constr 0 [.List ins, .List refs, .List outs, .I fee, .Map mint,
      .List certs, .Map withdrawals, range, .List sigs, .Map reds, .Map datums,
      .B txid, .Map votes, .List proposals, treasury, donation], redeemer, info] =>
    some ⟨ins, refs, outs, fee, mint, certs, withdrawals, range, sigs, reds,
      datums, txid, votes, proposals, treasury, donation, redeemer, info⟩
  | _ => none

theorem decode_encode (v : View) : decode (encode v) = some v := by cases v; rfl

theorem encode_decoded (d : Data) (v : View) (h : decode d = some v) : encode v = d := by
  unfold decode at h
  split at h
  · have hv := Option.some.inj h
    subst v
    rfl
  · simp at h

/-- Deliberately weaker than full context validity: no recursive field typing,
    hash-length, Value canonicality, ordering or ledger invariant is asserted. -/
def WellShaped (d : Data) : Prop := (decode d).isSome = true

def empty : View :=
  ⟨[], [], [], 0, [], [], [],
    .Constr 0 [.Constr 0 [.Constr 0 [], .Constr 1 []],
      .Constr 0 [.Constr 2 [], .Constr 1 []]],
    [], [], [], ⟨String.mk (List.replicate 32 (Char.ofNat 0))⟩, [], [],
    .Constr 1 [], .Constr 1 [], .I 0,
    .Constr 1 [.Constr 0 [.B ⟨String.mk (List.replicate 32 (Char.ofNat 0))⟩, .I 0], .Constr 1 []]⟩

def viewOf (d : Data) : View := (decode d).getD empty

theorem encode_viewOf (d : Data) (h : WellShaped d) : encode (viewOf d) = d := by
  cases hd : decode d with
  | none => simp [WellShaped, hd] at h
  | some v => simpa [viewOf, hd] using encode_decoded d v hd

/-- The actual isValidContext must provide this fact. It is a parameter with
    an explicit proof obligation, never an axiom or a replacement validity
    predicate silently identifying well-shaped data with valid contexts. -/
structure ValidityContract where
  isValidContext : Data → Prop
  wellShaped : ∀ d, isValidContext d → WellShaped d

/-- All valid raw contexts are covered; only validity restricts the view.
    In particular, no field is set to the placeholder to obtain this theorem. -/
theorem transport (validity : ValidityContract) (P : Data → Prop) :
    (∀ d, validity.isValidContext d → P d) ↔
      (∀ v, validity.isValidContext (encode v) → P (encode v)) := by
  exact forall_valid_encode_iff encode validity.isValidContext
    (fun d hd => ⟨viewOf d, encode_viewOf d (validity.wellShaped d hd)⟩) P

def rawArgs (d : Data) : List Term := [.Const (.Data d)]
def viewArgs (v : View) : List Term := rawArgs (encode v)

/-- A spending-purpose slice with all transaction fields and all payloads
    free. This is used for a proof calibration, not to fix unrelated fields. -/
def spendArgs (v : View) (ownId : ByteString) (ownIndex : Int) (datum : Option Data) : List Term :=
  let encodedDatum := match datum with | none => Data.Constr 1 [] | some d => .Constr 0 [d]
  viewArgs { v with info := .Constr 1 [.Constr 0 [.B ownId, .I ownIndex], encodedDatum] }

end ContextCorpus
