import Blaster

import PlutusCore.Crypto.Hash

namespace PlutusCore.Crypto.Hash.Tests.AxiomsBlasterProbe

open PlutusCore.ByteString
open PlutusCore.Crypto.Hash
open PlutusCore.Crypto.Hash.Axioms (NoCollision)

/- Without the axioms, the hash functions are opaque. -/
#blaster (solve-result: 1) (gen-cex: 0) [∀ (a b : ByteString), ripemd_160 a ≠ sha2_256 b]

#blaster [Axioms.LengthAlg → ∀ (a b : ByteString), ripemd_160 a ≠ sha2_256 b]

/- The 28-vs-32 pair, i.e. the two BLAKE2b widths are never confusable. -/
#blaster [Axioms.LengthAlg → ∀ (a b : ByteString), blake2b_224 a ≠ blake2b_256 b]

/- The width in the shape the Plutus builtin has: `Integer`-valued. -/
#blaster [Axioms.LengthAlg → ∀ (b : ByteString), lengthOfByteString (keccak_256 b) = 32]

/- A digest is never the empty bytestring. -/
#blaster [Axioms.LengthAlg → ∀ (b : ByteString), blake2b_256 b ≠ emptyByteString]

/- Handling collisions. -/
#blaster [Axioms.CollisionAlg → ∀ (a b : ByteString), NoCollision a b → blake2b_256 a = blake2b_256 b → a = b]

/- And the distinctness direction, which is now derived rather than assumed. -/
#blaster [Axioms.CollisionAlg → ∀ (a b : ByteString), NoCollision a b → a ≠ b → sha2_256 a ≠ sha2_256 b]

/- The full twelve-conjunct `BlasterAlg`, driving a conclusion that needs both halves. -/
#blaster [Axioms.AllAlg → ∀ (a b : ByteString), Axioms.NoCollision a b → (keccak_256 a = keccak_256 b → a = b) ∧ (keccak_256 a).length = 32]

/- Satisfiability -/
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.LengthAlg    → False]
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.CollisionAlg → False]
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.AllAlg       → False]

/- Collisions can happen if not excluded. -/
#blaster (solve-result: 1) (gen-cex: 0) [Axioms.CollisionAlg → ∀ (a b : ByteString), a ≠ b → sha2_256 a ≠ sha2_256 b]

end PlutusCore.Crypto.Hash.Tests.AxiomsBlasterProbe
