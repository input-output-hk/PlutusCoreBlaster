import Tests.ByteString.Blaster

/-! # Byte strings read and written with the solver

The goals of "`Spec` is enough" in `Tests.ByteString.Blaster` that need the solver, proved by
Blaster to the end. They
need the solver that CI builds; elsewhere they fail with "unknown tactic recfun-finder". Each is
also proved in Lean there. -/

namespace Tests.ByteString.SymbolicReads

open Tests.ByteString.Blaster
  (indexCons consIndex bstoiTwo bstoiTwoCek readBitOne literalIndex)
open PlutusCore.Bytes (byteStr)
open PlutusCore.ByteString (ByteString indexByteString)

theorem indexCons_solved : indexCons := by blaster (timeout: 60)
theorem consIndex_solved : consIndex := by blaster (timeout: 60)
theorem bstoiTwo_solved : bstoiTwo := by blaster (timeout: 60)
theorem bstoiTwoCek_solved : bstoiTwoCek := by blaster (timeout: 60)
theorem readBitOne_solved : readBitOne := by blaster (timeout: 60)
theorem literalIndex_solved : literalIndex := by blaster (timeout: 60)

-- Without `Spec`, nothing ties `uncons` to the bytes, so the first goal fails.
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 60)
  [∀ (k : Nat) (bs : ByteString), k < 256 → indexByteString ⟨byteStr k ++ bs.data⟩ 0 = .ok k]

end Tests.ByteString.SymbolicReads
