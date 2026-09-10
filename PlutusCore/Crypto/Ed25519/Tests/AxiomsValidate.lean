import PlutusCore.Crypto.Ed25519

namespace PlutusCore.Crypto.Ed25519.Tests.AxiomsValidate

open PlutusCore.ByteString
open PlutusCore.Crypto.Ed25519
open PlutusCore.Crypto.Ed25519.Axioms

/-! ## Validation of the Ed25519 axioms.

    Two things are checked here.

    First, the axioms that talk about the builtin are sampled on the vectors of the Plutus
    conformance suite, under
    `test-cases/uplc/evaluation/builtin/semantics/verifyEd25519Signature/`.  `opaque`
    definitions still compile, so `#guard` runs the real builtin; the result is read through
    `Except.toOption`, which is the `.error`/`.ok b` distinction the axioms are phrased in
    and is insensitive to the wording of the error message.

    Second, the axiom set is shown to be satisfiable, by exhibiting a model of `AllSpec`.
    This is the Lean counterpart of the `#blaster ... → False` probes: those ask Z3 for a
    model, which it does not manage to build once the constraint ties the result of an
    uninterpreted function to the *lengths* of its arguments. -/

/-! ### Vectors -/

/-- RFC 8032 vector, accepted (conformance `test-vector-02`). -/
private def tv02Pk : ByteString :=
  "\x3d\x40\x17\xc3\xe8\x43\x89\x5a\x92\xb7\x0a\xa7\x4d\x1b\x7e\xbc\
   \x9c\x98\x2c\xcf\x2e\xc4\x96\x8c\xc0\xcd\x55\xf1\x2a\xf4\x66\x0c"
private def tv02Msg : ByteString :=
  "\x72"
private def tv02Sig : ByteString :=
  "\x92\xa0\x09\xa9\xf0\xd4\xca\xb8\x72\x0e\x82\x0b\x5f\x64\x25\x40\
   \xa2\xb2\x7b\x54\x16\x50\x3f\x8f\xb3\x76\x22\x23\xeb\xdb\x69\xda\
   \x08\x5a\xc1\xe4\x3e\x15\x99\x6e\x45\x8f\x36\x13\xd0\xf1\x1d\x8c\
   \x38\x7b\x2e\xae\xb4\x30\x2a\xee\xb0\x0d\x29\x16\x12\xbb\x0c\x00"

/-- Well formed but rejected (conformance `test-vector-05`). -/
private def tv05Pk : ByteString :=
  "\x6d\xf9\x34\x0c\x13\x8c\xc1\x88\xb5\xfe\x44\x64\xeb\xaa\x3f\x7f\
   \xc2\x06\xa2\xd5\x5c\x34\x34\x70\x7e\x74\xc9\xfc\x04\xe2\x0e\xbb"
private def tv05Msg : ByteString :=
  "\x5f\x4c\x89\x89"
private def tv05Sig : ByteString :=
  "\x12\x4f\x6f\xc6\xb0\xd1\x00\x84\x27\x69\xe7\x1b\xd5\x30\x66\x4d\
   \x88\x8d\xf8\x50\x7d\xf6\xc5\x6d\xed\xfd\xb5\x09\xae\xb9\x34\x16\
   \xe2\x6b\x91\x8d\x38\xaa\x06\x30\x5d\xf3\x09\x56\x97\xc1\x8b\x2a\
   \xa8\x32\xea\xa5\x2e\xdc\x0a\xe4\x9f\xba\xe5\xa8\x5e\x15\x0c\x07"

/-- 31-byte key: outside the domain (conformance `short-key`). -/
private def shortKeyPk : ByteString :=
  "\xe2\x53\xaf\x07\x66\x80\x4b\x86\x9b\xb1\x59\x5b\xe9\x76\x5b\x53\
   \x48\x86\xbb\xaa\xb8\x30\x5b\xf5\x0d\xbc\x7f\x89\x9b\xfb\x5f"
private def shortKeyMsg : ByteString :=
  "\x18\xb6\xbe\xc0\x97"
private def shortKeySig : ByteString :=
  "\xb2\xfc\x46\xad\x47\xaf\x46\x44\x78\xc1\x99\xe1\xf8\xbe\x16\x9f\
   \x1b\xe6\x32\x7c\x7f\x9a\x0a\x66\x89\x37\x1c\xa9\x4c\xaf\x04\x06\
   \x4a\x01\xb2\x2a\xff\x15\x20\xab\xd5\x89\x51\x34\x16\x03\xfa\xed\
   \x76\x8c\xf7\x8c\xe9\x7a\xe7\xb0\x38\xab\xfe\x45\x6a\xa1\x7c\x09"

/-- 33-byte key: outside the domain (conformance `long-key`). -/
private def longKeyPk : ByteString :=
  "\xe2\x53\xaf\x07\x66\x80\x4b\x86\x9b\xb1\x59\x5b\xe9\x76\x5b\x53\
   \x48\x86\xbb\xaa\xb8\x30\x5b\xf5\x0d\xbc\x7f\x89\x9b\xfb\x5f\x01\
   \x01"
private def longKeyMsg : ByteString :=
  "\x18\xb6\xbe\xc0\x97"
private def longKeySig : ByteString :=
  "\xb2\xfc\x46\xad\x47\xaf\x46\x44\x78\xc1\x99\xe1\xf8\xbe\x16\x9f\
   \x1b\xe6\x32\x7c\x7f\x9a\x0a\x66\x89\x37\x1c\xa9\x4c\xaf\x04\x06\
   \x4a\x01\xb2\x2a\xff\x15\x20\xab\xd5\x89\x51\x34\x16\x03\xfa\xed\
   \x76\x8c\xf7\x8c\xe9\x7a\xe7\xb0\x38\xab\xfe\x45\x6a\xa1\x7c\x09"

/-- 63-byte signature: outside the domain (conformance `short-sig`). -/
private def shortSigPk : ByteString :=
  "\xe2\x53\xaf\x07\x66\x80\x4b\x86\x9b\xb1\x59\x5b\xe9\x76\x5b\x53\
   \x48\x86\xbb\xaa\xb8\x30\x5b\xf5\x0d\xbc\x7f\x89\x9b\xfb\x5f\x01"
private def shortSigMsg : ByteString :=
  "\x18\xb6\xbe\xc0\x97"
private def shortSigSig : ByteString :=
  "\xb2\xfc\x46\xad\x47\xaf\x46\x44\x78\xc1\x99\xe1\xf8\xbe\x16\x9f\
   \x1b\xe6\x32\x7c\x7f\x9a\x0a\x66\x89\x37\x1c\xa9\x4c\xaf\x04\x06\
   \x4a\x01\xb2\x2a\xff\x15\x20\xab\xd5\x89\x51\x34\x16\x03\xfa\xed\
   \x76\x8c\xf7\x8c\xe9\x7a\xe7\xb0\x38\xab\xfe\x45\x6a\xa1\x7c"

/-- 65-byte signature: outside the domain (conformance `long-sig`). -/
private def longSigPk : ByteString :=
  "\xe2\x53\xaf\x07\x66\x80\x4b\x86\x9b\xb1\x59\x5b\xe9\x76\x5b\x53\
   \x48\x86\xbb\xaa\xb8\x30\x5b\xf5\x0d\xbc\x7f\x89\x9b\xfb\x5f\x01"
private def longSigMsg : ByteString :=
  "\x18\xb6\xbe\xc0\x97"
private def longSigSig : ByteString :=
  "\xb2\xfc\x46\xad\x47\xaf\x46\x44\x78\xc1\x99\xe1\xf8\xbe\x16\x9f\
   \x1b\xe6\x32\x7c\x7f\x9a\x0a\x66\x89\x37\x1c\xa9\x4c\xaf\x04\x06\
   \x4a\x01\xb2\x2a\xff\x15\x20\xab\xd5\x89\x51\x34\x16\x03\xfa\xed\
   \x76\x8c\xf7\x8c\xe9\x7a\xe7\xb0\x38\xab\xfe\x45\x6a\xa1\x7c\x09\
   \x09"

/-! ### The sizes the vectors are meant to have -/

example : tv02Pk.length      = 32 := by rfl
example : tv02Sig.length     = 64 := by rfl
example : shortKeyPk.length  = 31 := by rfl
example : longKeyPk.length   = 33 := by rfl
example : shortSigSig.length = 63 := by rfl
example : longSigSig.length  = 65 := by rfl

/-! ### `verifyEd25519Signature_isOk`: the result domain

    A 32-byte key and a 64-byte signature give a boolean, whatever that boolean is, and
    anything else fails.  The message is never part of the domain: `test-vector-02` has a
    one-byte message and `long-sig` a five-byte one. -/

#guard (verifyEd25519Signature tv02Pk tv02Msg tv02Sig).toOption == some true
#guard (verifyEd25519Signature tv05Pk tv05Msg tv05Sig).toOption == some false

#guard (verifyEd25519Signature shortKeyPk shortKeyMsg shortKeySig).toOption == none
#guard (verifyEd25519Signature longKeyPk  longKeyMsg  longKeySig ).toOption == none
#guard (verifyEd25519Signature shortSigPk shortSigMsg shortSigSig).toOption == none
#guard (verifyEd25519Signature longSigPk  longSigMsg  longSigSig ).toOption == none

/-- A key that parses to no curve point is a plain rejection, not a failure: the domain
    really is about sizes only.  Here the key is 32 bytes of `0xff`, which is not a valid
    compressed Edwards point. -/
private def offCurvePk : ByteString :=
  "\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\
   \xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"

#guard (verifyEd25519Signature offCurvePk tv02Msg tv02Sig).toOption == some false

/- Tampering with the message is a rejection too, never a failure. -/
#guard (verifyEd25519Signature tv02Pk ⟨"\x73"⟩ tv02Sig).toOption == some false

/-! ### The axiom set is satisfiable

    A model of `AllSpec`: the verifier accepts exactly on the domain, and the key holder is
    taken to have signed the empty message only.  `NoForgery` is the guard that rules out
    everything else, which is what makes guarded unforgeability and guarded message binding
    hold at once. -/

private def mockVerify (pk _msg sig : ByteString) : Except String Bool :=
  if pk.length == 32 && sig.length == 64 then .ok true else .error "out of domain"

private def mockSigned (pk msg sig : ByteString) : Prop :=
  mockVerify pk msg sig = .ok true ∧ msg = emptyByteString

private def mockNoForgery (pk msg sig : ByteString) : Prop :=
  mockVerify pk msg sig = .ok true → msg = emptyByteString

private theorem mock_domain : DomainSpec mockVerify := by
  intro pk msg sig
  unfold mockVerify
  cases h : (pk.length == 32 && sig.length == 64) <;> rfl

private theorem mock_forgery : ForgerySpec mockVerify mockSigned mockNoForgery := by
  refine ⟨?_, ?_, ?_⟩
  . intro pk msg sig hs
    exact hs.left
  . intro pk msg sig hn hv
    exact ⟨hv, hn hv⟩
  . intro pk msg msg' sig _ _ hs hs'
    rw [hs.right, hs'.right]

theorem allSpec_satisfiable :
  ∃ (V : ByteString → ByteString → ByteString → Except String Bool)
    (S N : ByteString → ByteString → ByteString → Prop), AllSpec V S N :=
      ⟨mockVerify, mockSigned, mockNoForgery, mock_domain, mock_forgery⟩

end PlutusCore.Crypto.Ed25519.Tests.AxiomsValidate
