import Blaster

import PlutusCore.Crypto.Ed25519

namespace PlutusCore.Crypto.Ed25519.Tests.AxiomsBlasterProbe

open PlutusCore.ByteString
open PlutusCore.Crypto.Ed25519
open PlutusCore.Crypto.Ed25519.Axioms (Signed NoForgery)

/- Without the axioms the builtin is opaque: nothing is known about its result. -/
#blaster (solve-result: 1) (gen-cex: 0)
  [∀ (pk msg sig : ByteString), pk.length ≠ 32 → verifyEd25519Signature pk msg sig ≠ .ok true]

/- ### The result domain -/

/- A key of the wrong size makes the builtin fail, whatever the message and signature. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  pk.length ≠ 32 → verifyEd25519Signature pk msg sig ≠ .ok true]

/- And so does a signature of the wrong size. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  sig.length ≠ 64 → verifyEd25519Signature pk msg sig ≠ .ok false]

/- Inside the domain the builtin always answers with a boolean. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg sig : ByteString),
  pk.length = 32 → sig.length = 64 → (verifyEd25519Signature pk msg sig).isOk = true]

/- The message never decides whether the builtin fails. -/
#blaster [Axioms.DomainAlg → ∀ (pk msg msg' sig : ByteString),
  (verifyEd25519Signature pk msg sig).isOk = (verifyEd25519Signature pk msg' sig).isOk]

/- ### Unforgeability -/

/- A genuine signature is accepted. -/
#blaster [Axioms.ForgeryAlg → ∀ (pk msg sig : ByteString),
  Signed pk msg sig → verifyEd25519Signature pk msg sig = .ok true]

/- Guarded, an accepting run is evidence that the key holder signed. -/
#blaster [Axioms.ForgeryAlg → ∀ (pk msg sig : ByteString),
  NoForgery pk msg sig → verifyEd25519Signature pk msg sig = .ok true → Signed pk msg sig]

/- The direction a validator argument uses: no signature, no accepting run. -/
#blaster [Axioms.ForgeryAlg → ∀ (pk msg sig : ByteString),
  NoForgery pk msg sig → ¬ Signed pk msg sig → verifyEd25519Signature pk msg sig ≠ .ok true]

/- No replay: a signature issued for one message is not accepted for another. -/
#blaster [Axioms.ForgeryAlg → ∀ (pk msg msg' sig : ByteString),
  NoForgery pk msg sig → NoForgery pk msg' sig → Signed pk msg sig → msg ≠ msg' →
    verifyEd25519Signature pk msg' sig ≠ .ok true]

/- ### Both halves at once -/

/- What the key holder signs is well formed -- correctness feeds the domain axiom. -/
#blaster [Axioms.AllAlg → ∀ (pk msg sig : ByteString),
  Signed pk msg sig → pk.length = 32 ∧ sig.length = 64]

/- ### Satisfiability

   Only the unforgeability half is probed here.  Falsifying `... → False` means Z3 has built
   a model of the premise, and it does not manage to build one for `DomainAlg`: that axiom
   ties the result of an uninterpreted function to the *lengths* of its arguments.  A model
   of the whole set, `AllSpec`, is exhibited and proved in `Tests/AxiomsValidate.lean`
   instead, which settles consistency once and for all. -/

#blaster (solve-result: 1) (gen-cex: 0) [Axioms.ForgeryAlg → False]

/- Unforgeability really is guarded: without `NoForgery` an accepting run proves nothing. -/
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.ForgeryAlg → ∀ (pk msg sig : ByteString),
  verifyEd25519Signature pk msg sig = .ok true → Signed pk msg sig]

/- And so is message binding. -/
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.ForgeryAlg → ∀ (pk msg msg' sig : ByteString),
  Signed pk msg sig → Signed pk msg' sig → msg = msg']

end PlutusCore.Crypto.Ed25519.Tests.AxiomsBlasterProbe
