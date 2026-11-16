import ContextCorpus.CountProperties

namespace ContextCorpus.CountProperties
open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Optimize
open PlutusCore.Data (Data)

private theorem normalize_nat_bound {A B : Prop} (n bound : Nat)
    (h : A ↔ (n : Int) ≤ (bound : Int) ∧ B) : A ↔ n ≤ bound ∧ B := by
  simpa only [Int.ofNat_le] using h

/-- The hypotheses on fuel are explicit; no bound on the input list is assumed. -/
theorem inputs_acceptance (p : Parameters) (fuel : Nat) :
    cekExecuteProgram corpusInputsCount.script (args p) fuel = .Halt (.VCon .Unit) ↔
      p.context.inputs.length ≤ 4 ∧ cost .inputs p < fuel := by
  apply normalize_nat_bound (n := p.context.inputs.length) (bound := 4)
  simpa [script, test, elements, contextElements] using accepts_iff .inputs p fuel

theorem outputs_acceptance (p : Parameters) (fuel : Nat) :
    cekExecuteProgram corpusOutputsCount.script (args p) fuel = .Halt (.VCon .Unit) ↔
      p.context.outputs.length ≤ 8 ∧ cost .outputs p < fuel := by
  apply normalize_nat_bound (n := p.context.outputs.length) (bound := 8)
  simpa [script, test, elements, contextElements] using accepts_iff .outputs p fuel

theorem certificates_acceptance (p : Parameters) (fuel : Nat) :
    cekExecuteProgram corpusCertificatesCount.script (args p) fuel = .Halt (.VCon .Unit) ↔
      p.context.certificates.length ≤ 3 ∧ cost .certificates p < fuel := by
  apply normalize_nat_bound (n := p.context.certificates.length) (bound := 3)
  simpa [script, test, elements, contextElements] using accepts_iff .certificates p fuel

theorem proposals_acceptance (p : Parameters) (fuel : Nat) :
    cekExecuteProgram corpusProposalsCount.script (args p) fuel = .Halt (.VCon .Unit) ↔
      0 < p.context.proposals.length ∧ cost .proposals p < fuel := by
  simpa [script, test, elements, contextElements] using accepts_iff .proposals p fuel

def encoded (p : Parameters) : Data :=
  match args p with
  | [.Const (.Data d)] => d
  | _ => .I 0

theorem args_eq_raw (p : Parameters) : args p = rawArgs (encoded p) := by rfl

theorem contextElements_encoded (c : Case) (p : Parameters) :
    contextElements c (viewOf (encoded p)) = elements c p := by
  cases c <;> rfl

def rawCost (c : Case) (ctx : Data) : Nat :=
  prefixCost c + 37 * (contextElements c (viewOf ctx)).length + 16 + postCost c

/-- Raw-context theorem for ANY validity predicate whose valid spending
    contexts are covered by the encoding. Coverage is a representation fact,
    not an execution assumption. In particular, it introduces no list bound.
    The ledger's actual validity predicate must still discharge this contract. -/
theorem valid_raw_acceptance (isValidContext : Data → Prop)
    (covers : ∀ ctx, isValidContext ctx → ∃ p : Parameters, encoded p = ctx)
    (c : Case) (fuel : Nat) :
    ∀ ctx, isValidContext ctx →
      (cekExecuteProgram (script c).script (rawArgs ctx) fuel = .Halt (.VCon .Unit) ↔
        test c (contextElements c (viewOf ctx)).length = true ∧ rawCost c ctx < fuel) := by
  intro ctx hv
  obtain ⟨p, rfl⟩ := covers ctx hv
  rw [← args_eq_raw, accepts_iff]
  simp only [rawCost, contextElements_encoded, cost]

theorem valid_raw_eventually_accepts (isValidContext : Data → Prop)
    (covers : ∀ ctx, isValidContext ctx → ∃ p : Parameters, encoded p = ctx)
    (c : Case) :
    ∀ ctx, isValidContext ctx →
      ((∃ fuel, cekExecuteProgram (script c).script (rawArgs ctx) fuel = .Halt (.VCon .Unit)) ↔
        test c (contextElements c (viewOf ctx)).length = true) := by
  intro ctx hv
  obtain ⟨p, rfl⟩ := covers ctx hv
  rw [← args_eq_raw, eventually_accepts_iff, contextElements_encoded]

-- No proof may escape through the solver placeholder or a sorry.
run_cmd do
  for name in #[``execution, ``accepts_iff, ``eventually_accepts_iff,
      ``inputs_acceptance, ``outputs_acceptance, ``certificates_acceptance,
      ``proposals_acceptance, ``valid_raw_acceptance, ``valid_raw_eventually_accepts,
      ``Fold.correct, ``Fold.run_eq, ``foldPlan_foldl,
      ``ListLength.run_summary, ``ListConsumer.Certificate.run_eq] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => #[``propext, ``Quot.sound, ``Classical.choice].contains n) do
      throwError "unexpected axiom: {name}, {axioms}"
  Lean.logInfo "four compiled count validators: all fuel, unbounded lists, no new axioms"

end ContextCorpus.CountProperties
