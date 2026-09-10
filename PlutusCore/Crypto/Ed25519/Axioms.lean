import PlutusCore.ByteString
import PlutusCore.Crypto.Ed25519.Basic

namespace PlutusCore.Crypto.Ed25519.Axioms

namespace Internal

open PlutusCore.ByteString

/-! ## Axiomatisation for the PlutusCore Ed25519 verification builtin function. -/

variable (pk msg msg' sig : ByteString)

/- ### The result domain

   `verifyEd25519Signature` answers `.error` -- an `EvaluationError` in the CEK machine --
   exactly when the public key is not 32 bytes long or the signature is not 64 bytes long.
   The message length is unconstrained.  Every other rejection, an unparseable key or a
   point off the curve included, is an ordinary `.ok false`. -/

axiom verifyEd25519Signature_isOk :
  (verifyEd25519Signature pk msg sig).isOk = (pk.length == 32 && sig.length == 64)

/- The two directions of the domain axiom, in the shape a goal usually needs them. -/

theorem verifyEd25519Signature_isOk_of_lengths :
  pk.length = 32 → sig.length = 64
  ---------------------------------
  → (verifyEd25519Signature pk msg sig).isOk = true :=
    by
      intro hpk hsig
      simp [verifyEd25519Signature_isOk]
      constructor <;> assumption

theorem verifyEd25519Signature_pk_length :
  (verifyEd25519Signature pk msg sig).isOk = true
  -----------------------------------------------
  → pk.length = 32 :=
    by
      rw [verifyEd25519Signature_isOk]
      intro h
      simp at h
      exact h.left

theorem verifyEd25519Signature_sig_length :
  (verifyEd25519Signature pk msg sig).isOk = true
  -----------------------------------------------
  → sig.length = 64 :=
    by
      rw [verifyEd25519Signature_isOk]
      intro h
      simp at h
      exact h.right

/- The error cases, phrased on the `Except` value itself: outside the domain the builtin
   never produces a boolean, so the CEK machine always fails. -/

theorem not_isOk_imp_ne_ok {r : Except String Bool} {b : Bool} :
  r.isOk = false
  --------------
  → r ≠ .ok b :=
    by
      intro h he
      rw [he] at h
      contradiction

theorem verifyEd25519Signature_ne_ok_of_pk_length (b : Bool) :
  pk.length ≠ 32
  --------------
  → verifyEd25519Signature pk msg sig ≠ .ok b :=
    by
      intro h
      apply not_isOk_imp_ne_ok
      rw [verifyEd25519Signature_isOk]
      cases hb : pk.length == 32 with
      | false => rfl
      | true  => exact absurd (eq_of_beq hb) h

theorem verifyEd25519Signature_ne_ok_of_sig_length (b : Bool) :
  sig.length ≠ 64
  ---------------
  → verifyEd25519Signature pk msg sig ≠ .ok b :=
    by
      intro h
      apply not_isOk_imp_ne_ok
      rw [verifyEd25519Signature_isOk]
      cases hb : sig.length == 64 with
      | false => exact Bool.and_false _
      | true  => exact absurd (eq_of_beq hb) h

/- The domain does not mention the message, so failure never depends on it. -/

theorem verifyEd25519Signature_isOk_message_irrelevant :
  (verifyEd25519Signature pk msg sig).isOk = (verifyEd25519Signature pk msg' sig).isOk :=
    by rw [verifyEd25519Signature_isOk, verifyEd25519Signature_isOk]

/- ### Unforgeability

   `Signed pk msg sig` reads: the holder of the private key belonging to `pk` issued `sig`
   for `msg`.  It is an uninterpreted predicate; nothing about it is known beyond the
   axioms below.

   `NoForgery pk msg sig` is the guard, exactly as `NoCollision` is for the hashes: it
   carves out the triples on which the cryptographic assumption is being made.  Stating
   unforgeability unguarded would let a caller conclude `Signed` from any accepting run,
   which is false in the presence of a forgery; the guard is what a caller has to discharge
   (typically by assumption) before drawing that conclusion. -/

axiom Signed : ByteString → ByteString → ByteString → Prop

axiom NoForgery : ByteString → ByteString → ByteString → Prop

/-- Correctness: a genuine signature is accepted. -/
axiom verifyEd25519Signature_of_signed :
  Signed pk msg sig → verifyEd25519Signature pk msg sig = .ok true

/-- Unforgeability, guarded: an accepted signature was issued by the key holder. -/
axiom signed_of_verifyEd25519Signature :
  NoForgery pk msg sig →
  verifyEd25519Signature pk msg sig = .ok true
  --------------------------------------------
  → Signed pk msg sig

/-- Message binding, guarded: one signature authenticates one message. -/
axiom signed_message_unique :
  NoForgery pk msg sig  →
  NoForgery pk msg' sig →
  Signed pk msg sig     →
  Signed pk msg' sig
  ------------------------
  → msg = msg'

/- What the key holder signs is well formed: the lengths come for free from correctness
   and the domain axiom. -/

theorem signed_pk_length :
  Signed pk msg sig
  -----------------
  → pk.length = 32 :=
    by
      intro h
      apply verifyEd25519Signature_pk_length pk msg sig
      rw [verifyEd25519Signature_of_signed pk msg sig h]
      rfl

theorem signed_sig_length :
  Signed pk msg sig
  -----------------
  → sig.length = 64 :=
    by
      intro h
      apply verifyEd25519Signature_sig_length pk msg sig
      rw [verifyEd25519Signature_of_signed pk msg sig h]
      rfl

/- The contrapositive of unforgeability, which is the direction a validator argument uses:
   without a signature from the key holder the check cannot be made to pass. -/

theorem not_verified_of_not_signed :
  NoForgery pk msg sig →
  ¬ Signed pk msg sig
  -----------------------
  → verifyEd25519Signature pk msg sig ≠ .ok true :=
    by
      intro hng hns hv
      exact hns (signed_of_verifyEd25519Signature pk msg sig hng hv)

/- No replay: a signature issued for one message is not accepted for another. -/

theorem not_verified_of_signed_other :
  NoForgery pk msg sig  →
  NoForgery pk msg' sig →
  Signed pk msg sig     →
  msg ≠ msg'
  ------------------------
  → verifyEd25519Signature pk msg' sig ≠ .ok true :=
    by
      intro hng hng' hs hne hv
      have hsv  : Signed pk msg' sig := by apply signed_of_verifyEd25519Signature <;> assumption
      have hsmu : msg = msg'         := by apply signed_message_unique            <;> assumption
      contradiction

/- ### Axiom bundles -/

/-- The result domain of the builtin. -/
def DomainSpec (V : ByteString → ByteString → ByteString → Except String Bool) : Prop :=
  ∀ (pk msg sig : ByteString), (V pk msg sig).isOk = (pk.length == 32 && sig.length == 64)

/-- Correctness, guarded unforgeability and guarded message binding. -/
def ForgerySpec
  (V : ByteString → ByteString → ByteString → Except String Bool)
  (S N : ByteString → ByteString → ByteString → Prop) : Prop :=
    (∀ (pk msg sig : ByteString), S pk msg sig → V pk msg sig = .ok true) ∧
    (∀ (pk msg sig : ByteString), N pk msg sig → V pk msg sig = .ok true → S pk msg sig) ∧
    (∀ (pk msg msg' sig : ByteString),
      N pk msg sig → N pk msg' sig → S pk msg sig → S pk msg' sig → msg = msg')

/-- The whole axiom set. -/
def AllSpec
  (V : ByteString → ByteString → ByteString → Except String Bool)
  (S N : ByteString → ByteString → ByteString → Prop) : Prop := DomainSpec V ∧ ForgerySpec V S N

def DomainAlg : Prop := DomainSpec verifyEd25519Signature

theorem domainAlg : DomainAlg := verifyEd25519Signature_isOk

def ForgeryAlg : Prop := ForgerySpec verifyEd25519Signature Signed NoForgery

theorem forgeryAlg : ForgeryAlg :=
  ⟨verifyEd25519Signature_of_signed, signed_of_verifyEd25519Signature, signed_message_unique⟩

def AllAlg : Prop := AllSpec verifyEd25519Signature Signed NoForgery

theorem allAlg : AllAlg := ⟨domainAlg, forgeryAlg⟩

end Internal

export Internal
  ( -- the result domain
    verifyEd25519Signature_isOk
    verifyEd25519Signature_isOk_of_lengths
    verifyEd25519Signature_pk_length
    verifyEd25519Signature_sig_length
    -- the error cases on the `Except` value
    not_isOk_imp_ne_ok
    verifyEd25519Signature_ne_ok_of_pk_length
    verifyEd25519Signature_ne_ok_of_sig_length
    verifyEd25519Signature_isOk_message_irrelevant
    -- the domain of the unforgeability axioms
    Signed
    NoForgery
    -- correctness, unforgeability, message binding
    verifyEd25519Signature_of_signed
    signed_of_verifyEd25519Signature
    signed_message_unique
    -- consequences, derived
    signed_pk_length
    signed_sig_length
    not_verified_of_not_signed
    not_verified_of_signed_other
    -- the axioms as bundles, with their witnesses
    DomainSpec
    ForgerySpec
    AllSpec
    DomainAlg
    domainAlg
    ForgeryAlg
    forgeryAlg
    AllAlg
    allAlg
  )

end PlutusCore.Crypto.Ed25519.Axioms
