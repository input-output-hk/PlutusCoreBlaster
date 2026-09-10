import Blaster

import PlutusCore.Crypto.Secp256k1

namespace PlutusCore.Crypto.Secp256k1.Tests.AxiomsBlasterProbe

open PlutusCore.ByteString
open PlutusCore.Crypto.Secp256k1
open PlutusCore.Crypto.Secp256k1.Axioms
  (ValidEcdsaPublicKey ValidEcdsaScalars ValidSchnorrPublicKey
   EcdsaSigned EcdsaNoForgery SchnorrSigned SchnorrNoForgery)

/- Without the axioms the builtins are opaque: nothing is known about their results. -/
#blaster (solve-result: 1) (gen-cex: 0)
  [∀ (pk msg sig : ByteString),
    msg.length ≠ 32 → verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok true]

/- ### The result domain -/

/- ECDSA fails on a message that is not a digest-sized 32 bytes. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  msg.length ≠ 32 → verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok true]

/- And on a key it cannot decompress, however long it is. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  ¬ ValidEcdsaPublicKey pk → verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok false]

/- And on a signature whose scalars are out of range. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  ¬ ValidEcdsaScalars sig → verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok true]

/- Inside the domain ECDSA always answers with a boolean. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  ValidEcdsaPublicKey pk → msg.length = 32 → ValidEcdsaScalars sig → sig.length = 64 →
    (verifyEcdsaSecp256k1Signature pk msg sig).isOk = true]

/- Schnorr fails on a key it cannot lift, and on a signature of the wrong size. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  ¬ ValidSchnorrPublicKey pk → verifySchnorrSecp256k1Signature pk msg sig ≠ .ok true]

#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  sig.length ≠ 64 → verifySchnorrSecp256k1Signature pk msg sig ≠ .ok true]

/- Schnorr hashes the message itself, so the message is not part of its domain. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg msg' sig : ByteString),
  (verifySchnorrSecp256k1Signature pk msg sig).isOk = true →
    (verifySchnorrSecp256k1Signature pk msg' sig).isOk = true]

/- The two key formats are never confusable, by size alone. -/
#blaster [Axioms.DomainAlg → ∀ (pk : ByteString),
  ValidEcdsaPublicKey pk → ¬ ValidSchnorrPublicKey pk]

/- An accepting ECDSA run pins down all three sizes. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  (verifyEcdsaSecp256k1Signature pk msg sig).isOk = true →
    pk.length = 33 ∧ msg.length = 32 ∧ sig.length = 64]

/- ### Unforgeability -/

/- A genuine signature is accepted, in either scheme. -/
#blaster [Axioms.EcdsaForgeryAlg → ∀ (pk msg sig : ByteString),
  EcdsaSigned pk msg sig → verifyEcdsaSecp256k1Signature pk msg sig = .ok true]

#blaster [Axioms.SchnorrForgeryAlg → ∀ (pk msg sig : ByteString),
  SchnorrSigned pk msg sig → verifySchnorrSecp256k1Signature pk msg sig = .ok true]

/- The direction a validator argument uses: no signature, no accepting run. -/
#blaster [Axioms.EcdsaForgeryAlg → ∀ (pk msg sig : ByteString),
  EcdsaNoForgery pk msg sig → ¬ EcdsaSigned pk msg sig →
    verifyEcdsaSecp256k1Signature pk msg sig ≠ .ok true]

#blaster [Axioms.SchnorrForgeryAlg → ∀ (pk msg sig : ByteString),
  SchnorrNoForgery pk msg sig → ¬ SchnorrSigned pk msg sig →
    verifySchnorrSecp256k1Signature pk msg sig ≠ .ok true]

/- No replay: a signature issued for one message is not accepted for another. -/
#blaster [Axioms.EcdsaForgeryAlg → ∀ (pk msg msg' sig : ByteString),
  EcdsaNoForgery pk msg sig → EcdsaNoForgery pk msg' sig →
  EcdsaSigned pk msg sig → msg ≠ msg' →
    verifyEcdsaSecp256k1Signature pk msg' sig ≠ .ok true]

#blaster [Axioms.SchnorrForgeryAlg → ∀ (pk msg msg' sig : ByteString),
  SchnorrNoForgery pk msg sig → SchnorrNoForgery pk msg' sig →
  SchnorrSigned pk msg sig → msg ≠ msg' →
    verifySchnorrSecp256k1Signature pk msg' sig ≠ .ok true]

/- ### Both halves at once -/

/- What the key holder signs is well formed -- correctness feeds the domain axioms. -/
#blaster [Axioms.AllAlg → ∀ (pk msg sig : ByteString),
  EcdsaSigned pk msg sig → ValidEcdsaPublicKey pk ∧ msg.length = 32 ∧ sig.length = 64]

#blaster [Axioms.AllAlg → ∀ (pk msg sig : ByteString),
  SchnorrSigned pk msg sig → pk.length = 32 ∧ sig.length = 64]

/- A key cannot carry signatures in both schemes at once. -/
#blaster [Axioms.AllAlg → ∀ (pk msg msg' sig sig' : ByteString),
  EcdsaSigned pk msg sig → ¬ SchnorrSigned pk msg' sig']

/- ### Satisfiability

   Only the unforgeability half is probed here.  Falsifying `... → False` means Z3 has built
   a model of the premise, and it does not manage to build one for `DomainAlg`: that axiom
   ties the result of an uninterpreted function to the *lengths* of its arguments.  A model
   of the whole set, `AllSpec`, is exhibited and proved in `Tests/AxiomsValidate.lean`
   instead, which settles consistency once and for all. -/

#blaster (solve-result: 1) (gen-cex: 0) [Axioms.EcdsaForgeryAlg   → False]
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.SchnorrForgeryAlg → False]
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.ForgeryAlg        → False]

/- Unforgeability really is guarded: without `EcdsaNoForgery` an accepting run proves nothing. -/
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.EcdsaForgeryAlg → ∀ (pk msg sig : ByteString),
  verifyEcdsaSecp256k1Signature pk msg sig = .ok true → EcdsaSigned pk msg sig]

/- And no uniqueness of the signature is claimed: ECDSA is malleable. -/
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.EcdsaForgeryAlg → ∀ (pk msg sig sig' : ByteString),
  EcdsaSigned pk msg sig → EcdsaSigned pk msg sig' → sig = sig']

end PlutusCore.Crypto.Secp256k1.Tests.AxiomsBlasterProbe
