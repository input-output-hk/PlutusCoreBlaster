import PlutusCore.ByteString
import PlutusCore.Crypto.Secp256k1.Basic

namespace PlutusCore.Crypto.Secp256k1.Axioms

namespace Internal

open PlutusCore.ByteString

/-! ## Axiomatisation for the PlutusCore Secp256k1 verification builtin functions. -/

variable (pk msg msg' sig : ByteString)

/- ### Well formed keys and signatures

   Both builtins reject some inputs with an `.error` -- an `EvaluationError` in the CEK
   machine -- rather than with `.ok false`, and the size of the input is not the whole
   story.  The three predicates below name the remaining conditions.  They are
   uninterpreted: only the axioms of this module say anything about them.

   * `ValidEcdsaPublicKey pk`: `pk` is 33 bytes and decompresses to a point of the curve,
     i.e. it carries a 0x02 or 0x03 prefix and an x coordinate whose y exists.
   * `ValidEcdsaScalars sig`: the two scalars of the 64 byte compact signature `sig`,
     r on the first half and s on the second, both lie strictly between zero and the group
     order.  The Plutus specification makes an out-of-range scalar a failure rather than a
     rejection, and the builtin follows it.
   * `ValidSchnorrPublicKey pk`: `pk` is 32 bytes and lifts to a point of the curve, i.e.
     it is below the field prime and its x coordinate has a y (BIP-340 `lift_x`). -/

axiom ValidEcdsaPublicKey : ByteString → Prop

axiom ValidEcdsaScalars : ByteString → Prop

axiom ValidSchnorrPublicKey : ByteString → Prop

axiom validEcdsaPublicKey_length   : ValidEcdsaPublicKey   pk → pk.length = 33
axiom validSchnorrPublicKey_length : ValidSchnorrPublicKey pk → pk.length = 32

/- The two key formats are never confusable, by size alone. -/

theorem not_validSchnorrPublicKey_of_validEcdsaPublicKey :
  ValidEcdsaPublicKey pk
  ----------------------
  → ¬ ValidSchnorrPublicKey pk :=
    by
      intro he hs
      have h33 : pk.length = 33 := validEcdsaPublicKey_length   pk he
      have h32 : pk.length = 32 := validSchnorrPublicKey_length pk hs
      rw [h33] at h32
      contradiction

/- ### The result domain

   `verifyEcdsaSecp256k1Signature` answers with a boolean exactly on a 33 byte well formed
   key, a 32 byte message -- the message *is* the digest here, the builtin does not hash --
   and a 64 byte signature whose scalars are in range. -/

axiom verifyEcdsaSecp256k1Signature_isOk :
  (verifyEcdsaSecp256k1Signature pk msg sig).isOk = true ↔
    (ValidEcdsaPublicKey pk ∧ msg.length = 32 ∧ ValidEcdsaScalars sig ∧ sig.length = 64)

/- `verifySchnorrSecp256k1Signature` answers with a boolean exactly on a 32 byte well formed
   key and a 64 byte signature. Unlike ECDSA it hashes the message itself, so the message
   may have any length. -/

axiom verifySchnorrSecp256k1Signature_isOk :
  (verifySchnorrSecp256k1Signature pk msg sig).isOk = true ↔
    (ValidSchnorrPublicKey pk ∧ sig.length = 64)

/- The two directions of the domain axioms, in the shape a goal usually needs them. -/

theorem verifyEcdsaSecp256k1Signature_isOk_of_valid :
  ValidEcdsaPublicKey pk →
  msg.length = 32        →
  ValidEcdsaScalars sig  →
  sig.length = 64
  -------------------------
  → (verifyEcdsaSecp256k1Signature pk msg sig).isOk = true :=
    by
      intro hpk hmsg hsig hlen
      exact (verifyEcdsaSecp256k1Signature_isOk pk msg sig).mpr ⟨hpk, hmsg, hsig, hlen⟩

theorem verifySchnorrSecp256k1Signature_isOk_of_valid :
  ValidSchnorrPublicKey pk →
  sig.length = 64
  ---------------------------
  → (verifySchnorrSecp256k1Signature pk msg sig).isOk = true :=
    by
      intro hpk hlen
      exact (verifySchnorrSecp256k1Signature_isOk pk msg sig).mpr ⟨hpk, hlen⟩

theorem verifyEcdsaSecp256k1Signature_pk_length :
  (verifyEcdsaSecp256k1Signature pk msg sig).isOk = true
  ------------------------------------------------------
  → pk.length = 33 :=
    by
      rw [verifyEcdsaSecp256k1Signature_isOk]
      rintro ⟨h, _⟩
      exact validEcdsaPublicKey_length _ h

theorem verifyEcdsaSecp256k1Signature_msg_length :
  (verifyEcdsaSecp256k1Signature pk msg sig).isOk = true
  ------------------------------------------------------
  → msg.length = 32 :=
    by
      rw [verifyEcdsaSecp256k1Signature_isOk]
      rintro ⟨_, h, _⟩
      assumption

theorem verifyEcdsaSecp256k1Signature_sig_length :
  (verifyEcdsaSecp256k1Signature pk msg sig).isOk = true
  ------------------------------------------------------
  → sig.length = 64 :=
    by
      rw [verifyEcdsaSecp256k1Signature_isOk]
      rintro ⟨_, _, _, h⟩
      assumption

theorem verifySchnorrSecp256k1Signature_pk_length :
  (verifySchnorrSecp256k1Signature pk msg sig).isOk = true
  --------------------------------------------------------
  → pk.length = 32 :=
    by
      rw [verifySchnorrSecp256k1Signature_isOk]
      rintro ⟨h, _⟩
      exact validSchnorrPublicKey_length _ h

theorem verifySchnorrSecp256k1Signature_sig_length :
  (verifySchnorrSecp256k1Signature pk msg sig).isOk = true
  --------------------------------------------------------
  → sig.length = 64 :=
    by
      rw [verifySchnorrSecp256k1Signature_isOk]
      rintro ⟨_, h⟩
      assumption

/- Outside the domain the builtins never produce a boolean, so the CEK machine fails. -/

theorem not_isOk_imp_ne_ok {r : Except String Bool} {b : Bool} :
  r.isOk = false → r ≠ .ok b :=
    by
      intro h he
      rw [he] at h
      contradiction

theorem isOk_eq_false_of_not : ∀ {r : Except String Bool},
  ¬ (r.isOk = true) → r.isOk = false :=
    by
      intro r h
      cases hr : r.isOk with
      | false => rfl
      | true  => contradiction

theorem verifyEcdsaSecp256k1Signature_ne_ok_of_invalid_key (b : Bool) :
  ¬ ValidEcdsaPublicKey pk
  ------------------------
  → verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok b :=
    by
      intro h
      apply not_isOk_imp_ne_ok
      apply isOk_eq_false_of_not
      rw [verifyEcdsaSecp256k1Signature_isOk]
      rintro ⟨h, _⟩
      contradiction

theorem verifyEcdsaSecp256k1Signature_ne_ok_of_msg_length (b : Bool) :
  msg.length ≠ 32
  ---------------
  → verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok b :=
    by
      intro h
      apply not_isOk_imp_ne_ok
      apply isOk_eq_false_of_not
      intro hok
      have hn : msg.length = 32 := verifyEcdsaSecp256k1Signature_msg_length _ _ _ hok
      contradiction

theorem verifyEcdsaSecp256k1Signature_ne_ok_of_sig_length (b : Bool) :
  sig.length ≠ 64
  ---------------
  → verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok b :=
    by
      intro h
      apply not_isOk_imp_ne_ok
      apply isOk_eq_false_of_not
      intro hok
      have hn : sig.length = 64 := verifyEcdsaSecp256k1Signature_sig_length _ _ _ hok
      contradiction

theorem verifySchnorrSecp256k1Signature_ne_ok_of_invalid_key (b : Bool) :
  ¬ ValidSchnorrPublicKey pk
  --------------------------
  → verifySchnorrSecp256k1Signature pk msg sig ≠ .ok b :=
    by
      intro h
      apply not_isOk_imp_ne_ok
      apply isOk_eq_false_of_not
      rw [verifySchnorrSecp256k1Signature_isOk]
      rintro ⟨hn, _⟩
      contradiction

theorem verifySchnorrSecp256k1Signature_ne_ok_of_sig_length (b : Bool) :
  sig.length ≠ 64
  ---------------
  → verifySchnorrSecp256k1Signature pk msg sig ≠ .ok b :=
    by
      intro h
      apply not_isOk_imp_ne_ok
      apply isOk_eq_false_of_not
      intro hok
      have hn := verifySchnorrSecp256k1Signature_sig_length _ _ _ hok
      contradiction

/- The Schnorr domain does not mention the message, so failure never depends on it. -/

theorem verifySchnorrSecp256k1Signature_isOk_message_irrelevant :
  (verifySchnorrSecp256k1Signature pk msg sig).isOk = true ↔
    (verifySchnorrSecp256k1Signature pk msg' sig).isOk = true :=
      by rw [verifySchnorrSecp256k1Signature_isOk, verifySchnorrSecp256k1Signature_isOk]

/- ### Unforgeability

   `EcdsaSigned pk msg sig` reads: the holder of the private key belonging to `pk` issued
   `sig` for `msg`, and `SchnorrSigned` says the same of the Schnorr scheme.  Both are
   uninterpreted; nothing about them is known beyond the axioms below.

   `EcdsaNoForgery` and `SchnorrNoForgery` are the guards, exactly as `NoCollision` is for
   the hashes: they carve out the triples on which the cryptographic assumption is being
   made.  A caller discharges the guard -- usually by assumption -- before reading an
   accepting run as evidence of a signature. -/

axiom EcdsaSigned : ByteString → ByteString → ByteString → Prop

axiom EcdsaNoForgery : ByteString → ByteString → ByteString → Prop

axiom SchnorrSigned : ByteString → ByteString → ByteString → Prop

axiom SchnorrNoForgery : ByteString → ByteString → ByteString → Prop

/-- Correctness: a genuine signature is accepted. -/
axiom verifyEcdsaSecp256k1Signature_of_signed :
  EcdsaSigned pk msg sig → verifyEcdsaSecp256k1Signature pk msg sig = .ok true

/-- Unforgeability, guarded: an accepted signature was issued by the key holder. -/
axiom ecdsaSigned_of_verifyEcdsaSecp256k1Signature :
  EcdsaNoForgery pk msg sig →
  verifyEcdsaSecp256k1Signature pk msg sig = .ok true
  ---------------------------------------------------
  → EcdsaSigned pk msg sig

/-- Message binding, guarded: one signature authenticates one message. -/
axiom ecdsaSigned_message_unique :
  EcdsaNoForgery pk msg sig  →
  EcdsaNoForgery pk msg' sig →
  EcdsaSigned pk msg sig     →
  EcdsaSigned pk msg' sig
  -----------------------------
  → msg = msg'

/-- Correctness: a genuine signature is accepted. -/
axiom verifySchnorrSecp256k1Signature_of_signed :
  SchnorrSigned pk msg sig → verifySchnorrSecp256k1Signature pk msg sig = .ok true

/-- Unforgeability, guarded: an accepted signature was issued by the key holder. -/
axiom schnorrSigned_of_verifySchnorrSecp256k1Signature :
  SchnorrNoForgery pk msg sig →
  verifySchnorrSecp256k1Signature pk msg sig = .ok true
  -----------------------------------------------------
  → SchnorrSigned pk msg sig

/-- Message binding, guarded: one signature authenticates one message. -/
axiom schnorrSigned_message_unique :
  SchnorrNoForgery pk msg sig  →
  SchnorrNoForgery pk msg' sig →
  SchnorrSigned pk msg sig     →
  SchnorrSigned pk msg' sig
  -------------------------------
  → msg = msg'

/- Note that no uniqueness of the *signature* is claimed. Signing draws a nonce, so one key
   and one message have many signatures that verify; only the message a signature commits to
   is pinned down.  The one twin the builtin does rule out is the malleable high-s form of an
   ECDSA signature -- Cardano insists on low s -- but that is a rejection, an ordinary
   `.ok false`, and nothing here rests on it. -/

/- What the key holder signs is well formed: the shapes come for free from correctness and
   the domain axioms. -/

theorem ecdsaSigned_valid_key :
  EcdsaSigned pk msg sig
  ----------------------
  → ValidEcdsaPublicKey pk :=
    by
      intro h
      apply And.left
      apply (verifyEcdsaSecp256k1Signature_isOk pk msg sig).mp
      rw [verifyEcdsaSecp256k1Signature_of_signed pk msg sig h]
      rfl

theorem ecdsaSigned_msg_length :
  EcdsaSigned pk msg sig
  ----------------------
  → msg.length = 32 :=
    by
      intro h
      apply verifyEcdsaSecp256k1Signature_msg_length pk msg sig
      rw [verifyEcdsaSecp256k1Signature_of_signed pk msg sig h]
      rfl

theorem ecdsaSigned_sig_length :
  EcdsaSigned pk msg sig
  ----------------------
  → sig.length = 64 :=
    by
      intro h
      apply verifyEcdsaSecp256k1Signature_sig_length pk msg sig
      rw [verifyEcdsaSecp256k1Signature_of_signed pk msg sig h]
      rfl

theorem schnorrSigned_valid_key :
  SchnorrSigned pk msg sig
  ------------------------
  → ValidSchnorrPublicKey pk :=
    by
      intro h
      apply And.left
      apply (verifySchnorrSecp256k1Signature_isOk pk msg sig).mp
      rw [verifySchnorrSecp256k1Signature_of_signed pk msg sig h]
      rfl

theorem schnorrSigned_sig_length :
  SchnorrSigned pk msg sig
  ------------------------
  → sig.length = 64 :=
    by
      intro h
      apply verifySchnorrSecp256k1Signature_sig_length pk msg sig
      rw [verifySchnorrSecp256k1Signature_of_signed pk msg sig h]
      rfl

/- The contrapositive of unforgeability, which is the direction a validator argument uses:
   without a signature from the key holder the check cannot be made to pass. -/

theorem not_verified_of_not_ecdsaSigned :
  EcdsaNoForgery pk msg sig →
  ¬ EcdsaSigned pk msg sig
  ----------------------------
  → verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok true :=
    by
      intro hng hns hv
      exact hns (ecdsaSigned_of_verifyEcdsaSecp256k1Signature pk msg sig hng hv)

theorem not_verified_of_not_schnorrSigned :
  SchnorrNoForgery pk msg sig →
  ¬ SchnorrSigned pk msg sig
  ------------------------------
  → verifySchnorrSecp256k1Signature pk msg sig ≠ .ok true :=
    by
      intro hng hns hv
      exact hns (schnorrSigned_of_verifySchnorrSecp256k1Signature pk msg sig hng hv)

/- No replay: a signature issued for one message is not accepted for another. -/

theorem not_verified_of_ecdsaSigned_other :
  EcdsaNoForgery pk msg sig  →
  EcdsaNoForgery pk msg' sig →
  EcdsaSigned pk msg sig     →
  msg ≠ msg'
  -----------------------------
  → verifyEcdsaSecp256k1Signature pk msg' sig ≠ .ok true :=
    by
      intro hng hng' hs hne hv
      have hsv  : EcdsaSigned pk msg' sig := by apply ecdsaSigned_of_verifyEcdsaSecp256k1Signature <;> assumption
      have hsmu : msg = msg'              := by apply ecdsaSigned_message_unique                   <;> assumption
      contradiction

theorem not_verified_of_schnorrSigned_other :
  SchnorrNoForgery pk msg sig  →
  SchnorrNoForgery pk msg' sig →
  SchnorrSigned pk msg sig     →
  msg ≠ msg'
  -------------------------------
  → verifySchnorrSecp256k1Signature pk msg' sig ≠ .ok true :=
    by
      intro hng hng' hs hne hv
      have hsv  : SchnorrSigned pk msg' sig := by apply schnorrSigned_of_verifySchnorrSecp256k1Signature <;> assumption
      have hsmu : msg = msg'                := by apply schnorrSigned_message_unique                     <;> assumption
      contradiction

/- ### Axiom bundles -/

/-- The result domain of both builtins, and the sizes the key predicates imply. -/
def DomainSpec
  (Ve Vs : ByteString → ByteString → ByteString → Except String Bool)
  (Ke Sc Ks : ByteString → Prop) : Prop :=
    (∀ (pk : ByteString), Ke pk → pk.length = 33) ∧
    (∀ (pk : ByteString), Ks pk → pk.length = 32) ∧
    (∀ (pk msg sig : ByteString),
      (Ve pk msg sig).isOk = true ↔ (Ke pk ∧ msg.length = 32 ∧ Sc sig ∧ sig.length = 64)) ∧
    (∀ (pk msg sig : ByteString),
      (Vs pk msg sig).isOk = true ↔ (Ks pk ∧ sig.length = 64))

/-- Correctness, guarded unforgeability and guarded message binding, for one scheme. -/
def SchemeForgerySpec
  (V : ByteString → ByteString → ByteString → Except String Bool)
  (S N : ByteString → ByteString → ByteString → Prop) : Prop :=
    (∀ (pk msg sig : ByteString), S pk msg sig → V pk msg sig = .ok true) ∧
    (∀ (pk msg sig : ByteString), N pk msg sig → V pk msg sig = .ok true → S pk msg sig) ∧
    (∀ (pk msg msg' sig : ByteString),
      N pk msg sig → N pk msg' sig → S pk msg sig → S pk msg' sig → msg = msg')

/-- The same, for both schemes at once. -/
def ForgerySpec
  (Ve Vs : ByteString → ByteString → ByteString → Except String Bool)
  (Se Ne Ss Ns : ByteString → ByteString → ByteString → Prop) : Prop :=
    SchemeForgerySpec Ve Se Ne ∧ SchemeForgerySpec Vs Ss Ns

/-- The whole axiom set. -/
def AllSpec
  (Ve Vs : ByteString → ByteString → ByteString → Except String Bool)
  (Ke Sc Ks : ByteString → Prop)
  (Se Ne Ss Ns : ByteString → ByteString → ByteString → Prop) : Prop :=
    DomainSpec Ve Vs Ke Sc Ks ∧ ForgerySpec Ve Vs Se Ne Ss Ns

def DomainAlg : Prop :=
  DomainSpec verifyEcdsaSecp256k1Signature verifySchnorrSecp256k1Signature
    ValidEcdsaPublicKey ValidEcdsaScalars ValidSchnorrPublicKey

theorem domainAlg : DomainAlg :=
  ⟨validEcdsaPublicKey_length, validSchnorrPublicKey_length,
   verifyEcdsaSecp256k1Signature_isOk, verifySchnorrSecp256k1Signature_isOk⟩

def EcdsaForgeryAlg : Prop :=
  SchemeForgerySpec verifyEcdsaSecp256k1Signature EcdsaSigned EcdsaNoForgery

theorem ecdsaForgeryAlg : EcdsaForgeryAlg :=
  ⟨verifyEcdsaSecp256k1Signature_of_signed,
   ecdsaSigned_of_verifyEcdsaSecp256k1Signature,
   ecdsaSigned_message_unique⟩

def SchnorrForgeryAlg : Prop :=
  SchemeForgerySpec verifySchnorrSecp256k1Signature SchnorrSigned SchnorrNoForgery

theorem schnorrForgeryAlg : SchnorrForgeryAlg :=
  ⟨verifySchnorrSecp256k1Signature_of_signed,
   schnorrSigned_of_verifySchnorrSecp256k1Signature,
   schnorrSigned_message_unique⟩

def ForgeryAlg : Prop :=
  ForgerySpec verifyEcdsaSecp256k1Signature verifySchnorrSecp256k1Signature
    EcdsaSigned EcdsaNoForgery SchnorrSigned SchnorrNoForgery

theorem forgeryAlg : ForgeryAlg := ⟨ecdsaForgeryAlg, schnorrForgeryAlg⟩

def AllAlg : Prop :=
  AllSpec verifyEcdsaSecp256k1Signature verifySchnorrSecp256k1Signature
    ValidEcdsaPublicKey ValidEcdsaScalars ValidSchnorrPublicKey
    EcdsaSigned EcdsaNoForgery SchnorrSigned SchnorrNoForgery

theorem allAlg : AllAlg := ⟨domainAlg, forgeryAlg⟩

end Internal

export Internal
  ( -- well formed keys and signatures
    ValidEcdsaPublicKey
    ValidEcdsaScalars
    ValidSchnorrPublicKey
    validEcdsaPublicKey_length
    validSchnorrPublicKey_length
    not_validSchnorrPublicKey_of_validEcdsaPublicKey
    -- the result domain
    verifyEcdsaSecp256k1Signature_isOk
    verifySchnorrSecp256k1Signature_isOk
    verifyEcdsaSecp256k1Signature_isOk_of_valid
    verifySchnorrSecp256k1Signature_isOk_of_valid
    verifyEcdsaSecp256k1Signature_pk_length
    verifyEcdsaSecp256k1Signature_msg_length
    verifyEcdsaSecp256k1Signature_sig_length
    verifySchnorrSecp256k1Signature_pk_length
    verifySchnorrSecp256k1Signature_sig_length
    -- the error cases on the `Except` value
    not_isOk_imp_ne_ok
    isOk_eq_false_of_not
    verifyEcdsaSecp256k1Signature_ne_ok_of_invalid_key
    verifyEcdsaSecp256k1Signature_ne_ok_of_msg_length
    verifyEcdsaSecp256k1Signature_ne_ok_of_sig_length
    verifySchnorrSecp256k1Signature_ne_ok_of_invalid_key
    verifySchnorrSecp256k1Signature_ne_ok_of_sig_length
    verifySchnorrSecp256k1Signature_isOk_message_irrelevant
    -- the domain of the unforgeability axioms
    EcdsaSigned
    EcdsaNoForgery
    SchnorrSigned
    SchnorrNoForgery
    -- correctness, unforgeability, message binding
    verifyEcdsaSecp256k1Signature_of_signed
    ecdsaSigned_of_verifyEcdsaSecp256k1Signature
    ecdsaSigned_message_unique
    verifySchnorrSecp256k1Signature_of_signed
    schnorrSigned_of_verifySchnorrSecp256k1Signature
    schnorrSigned_message_unique
    -- consequences, derived
    ecdsaSigned_valid_key
    ecdsaSigned_msg_length
    ecdsaSigned_sig_length
    schnorrSigned_valid_key
    schnorrSigned_sig_length
    not_verified_of_not_ecdsaSigned
    not_verified_of_not_schnorrSigned
    not_verified_of_ecdsaSigned_other
    not_verified_of_schnorrSigned_other
    -- the axioms as bundles, with their witnesses
    DomainSpec
    SchemeForgerySpec
    ForgerySpec
    AllSpec
    DomainAlg
    domainAlg
    EcdsaForgeryAlg
    ecdsaForgeryAlg
    SchnorrForgeryAlg
    schnorrForgeryAlg
    ForgeryAlg
    forgeryAlg
    AllAlg
    allAlg
  )

end PlutusCore.Crypto.Secp256k1.Axioms
