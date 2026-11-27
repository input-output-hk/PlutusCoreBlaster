import PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)
open PlutusCore.UPLC.Term (Program Term)

/-! ## Theorems on iteration of the CEK `step` function. -/

/-! ### Iteration of `step` -/

def stepN (sv : BuiltinSemanticsVariant) (s : State) : Nat → State
  | 0 => s
  | (n + 1) => stepN sv (step sv s) n

/-! ### Terminal states -/

/-- A state the machine stops on. -/
def terminal (s : State) : Prop := (∃ V, s = State.Halt V) ∨ s = State.Error ∨ s = State.BudgetExhausted

instance : DecidablePred terminal := fun s =>
  match s with
  | State.Halt V => isTrue (Or.inl ⟨V, rfl⟩)
  | State.Error => isTrue (Or.inr (Or.inl rfl))
  | State.BudgetExhausted => isTrue (Or.inr (Or.inr rfl))
  | State.Eval _ _ _ => isFalse (by rintro (⟨V, h⟩ | h) <;> cases h <;> contradiction)
  | State.Return _ _ => isFalse (by rintro (⟨V, h⟩ | h) <;> cases h <;> contradiction)

/-- `step` fixes exactly the terminal states. -/
theorem step_fix_iff (sv : BuiltinSemanticsVariant) (s : State) :
    step sv s = s ↔ terminal s := by
  refine ⟨fun h => ?_, fun h => by
           rcases h with ⟨V, rfl⟩
           . rfl
           . rename_i h2 <;> cases h2 <;> rename_i h2 <;> rw [h2] <;> simp [step]
         ⟩
  cases s with
  | Halt V => exact Or.inl ⟨V, rfl⟩
  | Error => exact Or.inr (Or.inl rfl)
  | BudgetExhausted => exact Or.inr (Or.inr rfl)
  | Eval st rho t => exact absurd h (by cases t <;> simp only [step] <;> (try split) <;> simp_all)
  | Return st v =>
      exact absurd h (by
        cases st <;> (try (rename_i f _; cases f)) <;> (try cases v) <;>
          simp only [step, evalBuiltin] <;> (repeat' split) <;> simp_all)

/-! ### Fuel composition -/

/-- Fuel composition for `stepN`, with no side condition. -/
theorem stepN_add (sv : BuiltinSemanticsVariant) (s : State) (n m : Nat) :
    stepN sv s (n + m) = stepN sv (stepN sv s n) m := by
  induction n generalizing s with
  | zero => simp [stepN]
  | succ p ih => rw [Nat.succ_add]; exact ih (step sv s)

/-- A terminal state is the state at every index of the run from it. -/
theorem stepN_of_terminal (sv : BuiltinSemanticsVariant) (s : State) (h : terminal s)
    (n : Nat) : stepN sv s n = s := by
  induction n with
  | zero => rfl
  | succ p ih =>
      show stepN sv (step sv s) p = s
      rw [(step_fix_iff sv s).mpr h]
      exact ih

/-- A run whose state at `n` is terminal is at that state at every index past `n`. -/
theorem stepN_fix (sv : BuiltinSemanticsVariant) (s : State) (n : Nat)
    (h : terminal (stepN sv s n)) (m : Nat) :
    stepN sv s (n + m) = stepN sv s n := by
  rw [stepN_add]
  exact stepN_of_terminal sv _ h m

/-! ### `runSteps` in terms of `stepN` -/

/-- `runSteps` returns the state at index `n` when that state is a `Halt` state, and
`State.Error` otherwise. -/
theorem runSteps_eq_stepN (sv : BuiltinSemanticsVariant) (s : State) (n : Nat) :
    runSteps sv s n =
      match stepN sv s n with
      | State.Halt V => State.Halt V
      | State.Error => State.Error
      | _ => State.BudgetExhausted := by
  induction n generalizing s with
  | zero => cases s <;> rfl
  | succ p ih =>
      cases s with
      | Halt V => rw [stepN_of_terminal sv _ (Or.inl ⟨V, rfl⟩)]; rfl
      | Error => rw [stepN_of_terminal sv _ (Or.inr (Or.inl rfl))]; rfl
      | BudgetExhausted => rw [stepN_of_terminal sv _ (Or.inr (Or.inr rfl))]; rfl
      | Eval st rho t => exact ih (step sv (State.Eval st rho t))
      | Return st v => exact ih (step sv (State.Return st v))

/-- The assurance runner retains unfinished states at the same step index as `stepN`. -/
theorem runStepsPreservingState_eq_stepN (sv : BuiltinSemanticsVariant) (s : State)
    (n : Nat) : runStepsPreservingState sv s n = stepN sv s n := by
  induction n generalizing s with
  | zero => cases s <;> rfl
  | succ n ih =>
      cases s with
      | Halt V =>
          simp only [runStepsPreservingState, stepN, step]
          exact (stepN_of_terminal sv (State.Halt V) (Or.inl ⟨V, rfl⟩) n).symm
      | Error =>
          simp only [runStepsPreservingState, stepN, step]
          exact (stepN_of_terminal sv State.Error (Or.inr (Or.inl rfl)) n).symm
      | BudgetExhausted =>
          simp only [runStepsPreservingState, stepN, step]
          exact (stepN_of_terminal sv State.BudgetExhausted (Or.inr (Or.inr rfl)) n).symm
      | Eval st rho t => exact ih (step sv (State.Eval st rho t))
      | Return st v => exact ih (step sv (State.Return st v))

/-! ### Program execution -/

/-- A program's halt result does not depend on how much fuel it was given, past enough. -/
theorem cekExecuteProgramWithSemanticVariant_halt_stable
    (sv : BuiltinSemanticsVariant) (p : Program) (params : List Term) (V : CekValue) (n m : Nat)
    (h : cekExecuteProgramWithSemanticVariant sv p params n = State.Halt V) :
    cekExecuteProgramWithSemanticVariant sv p params (n + m) = State.Halt V := by
  cases p with
  | Program ver body =>
      simp only [cekExecuteProgramWithSemanticVariant, runSteps_eq_stepN] at h ⊢
      have hs : stepN sv (initialState (applyParams body params)) n = State.Halt V := by
        split at h <;> simp_all
      rw [stepN_fix sv _ n (Or.inl ⟨V, hs⟩) m, hs]

section CaseBranch

open PlutusCore.Data (Data)
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-! ### `case` branch selection -/

@[simp] theorem caseBranch_nil (i : Int) : caseBranch [] i = none := rfl

@[simp] theorem caseBranch_cons (M : Term) (Ms : List Term) (i : Int) :
  caseBranch (M :: Ms) i = if i = 0 then some M else caseBranch Ms (i - 1) := rfl

/-- `caseBranch` selects exactly the branch that the `case` rule of the Plutus
    reference implementation selects for an integer scrutinee: the `i`-th branch
    when `0 ≤ i` and it exists, an error otherwise. -/
theorem caseBranch_eq_getElem? (Ms : List Term) (i : Int) :
  caseBranch Ms i = if 0 ≤ i then Ms[i.toNat]? else none := by
  induction Ms generalizing i with
  | nil => simp
  | cons M Ms ih =>
    rw [caseBranch_cons]
    by_cases h : i = 0
    . subst h; simp
    . rw [if_neg h, ih]
      by_cases h0 : 0 ≤ i
      . have h1 : 0 ≤ i - 1 := by omega
        have h2 : i.toNat = (i - 1).toNat + 1 := by omega
        rw [if_pos h1, if_pos h0, h2]
        simp
      . have h1 : ¬ (0 ≤ i - 1) := by omega
        rw [if_neg h1, if_neg h0]

/-! ### `Frame.CaseScrutinee`

    The `Frame.CaseScrutinee` rule is written so that the `match` on the returned
    value never looks below the `Const` constructor, and so that an integer tag
    never appears as a `match` discriminant; both are needed for the SMT backend
    to be able to reduce a `case`.  The theorems below pin the resulting
    behaviour to the more direct formulation they replace.
-/

variable (v : BuiltinSemanticsVariant) (Ms : List Term) (ρ : Environment) (s : Stack)

theorem step_case_integer (n : Int) :
  step v (State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.Integer n)))
    = (if 0 ≤ n && n.toNat < Ms.length then
         match Ms[n.toNat]? with
         | some mi => State.Eval s ρ mi
         | none => State.Error
       else State.Error) := by
  show (match caseBranch Ms n with
        | some mi => State.Eval s ρ mi
        | none => State.Error) = _
  rw [caseBranch_eq_getElem?]
  by_cases h0 : 0 ≤ n
  . by_cases h1 : n.toNat < Ms.length
    . rw [if_pos h0, if_pos (by simp [h0, h1])]
    . rw [if_pos h0, if_neg (by simp [h1]), List.getElem?_eq_none (by omega)]
  . rw [if_neg h0, if_neg (by simp [h0])]

theorem step_case_bool (b : Bool) :
  step v (State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.Bool b)))
    = (match b with
       | false =>
         if Ms.length == 1 || Ms.length == 2 then
           match List.get?Internal Ms 0 with
           | some mi => State.Eval s ρ mi
           | none => State.Error
         else State.Error
       | true =>
         if Ms.length == 2 then
           match List.get?Internal Ms 1 with
           | some mi => State.Eval s ρ mi
           | none => State.Error
         else State.Error) := by
  cases b <;> rfl

theorem step_case_constList (l : List Const) :
  step v (State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstList l)))
    = (match l with
       | c :: cs =>
         if Ms.length == 1 || Ms.length == 2 then
           match List.get?Internal Ms 0 with
           | some mi =>
             State.Eval (step.folding [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)] s) ρ mi
           | none => State.Error
         else State.Error
       | [] =>
         if Ms.length == 2 then
           match List.get?Internal Ms 1 with
           | some mi => State.Eval s ρ mi
           | none => State.Error
         else State.Error) := by
  cases l <;> rfl

theorem step_case_constDataList (l : List Data) :
  step v (State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstDataList l)))
    = (match l with
       | c :: cs =>
         if Ms.length == 1 || Ms.length == 2 then
           match List.get?Internal Ms 0 with
           | some mi =>
             State.Eval
               (step.folding [CekValue.VCon (.Data c), CekValue.VCon (Const.ConstDataList cs)] s) ρ mi
           | none => State.Error
         else State.Error
       | [] =>
         if Ms.length == 2 then
           match List.get?Internal Ms 1 with
           | some mi => State.Eval s ρ mi
           | none => State.Error
         else State.Error) := by
  cases l <;> rfl

theorem step_case_constPairDataList (l : List (Data × Data)) :
  step v (State.Return (Frame.CaseScrutinee Ms ρ :: s) (CekValue.VCon (Const.ConstPairDataList l)))
    = (match l with
       | c :: cs =>
         if Ms.length == 1 || Ms.length == 2 then
           match List.get?Internal Ms 0 with
           | some mi =>
             State.Eval
               (step.folding [CekValue.VCon (.PairData c),
                              CekValue.VCon (Const.ConstPairDataList cs)] s) ρ mi
           | none => State.Error
         else State.Error
       | [] =>
         if Ms.length == 2 then
           match List.get?Internal Ms 1 with
           | some mi => State.Eval s ρ mi
           | none => State.Error
         else State.Error) := by
  cases l <;> rfl

end CaseBranch

end PlutusCore.UPLC.CekMachine
