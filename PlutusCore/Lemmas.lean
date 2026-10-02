namespace PlutusCore

/-- Completeness out of reflexivity, for any `Bool`-valued comparison. -/
theorem eq_false_imp_ne {α : Type} {cmp : α → α → Bool} (refl : ∀ a, cmp a a = true)
    {a b : α} (h : cmp a b = false) : a ≠ b := by
  intro heq
  rw [heq, refl b] at h
  exact Bool.noConfusion h

end PlutusCore
