namespace ContextCorpus

/-- Representation-independent quantifier transport. Only coverage of valid
    inputs is required; neither finite domains nor bounded containers are used.
    The validity predicate is retained on both sides. -/
theorem forall_valid_encode_iff {Raw View : Type}
    (encode : View → Raw) (valid : Raw → Prop)
    (covers : ∀ d, valid d → ∃ v, encode v = d) (P : Raw → Prop) :
    (∀ d, valid d → P d) ↔ (∀ v, valid (encode v) → P (encode v)) := by
  constructor
  · intro h v hv; exact h _ hv
  · intro h d hd
    obtain ⟨v, hv⟩ := covers d hd
    subst d
    exact h v hd

end ContextCorpus
