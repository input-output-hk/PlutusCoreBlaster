import PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Data (Data)
open PlutusCore.Default
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-! ## Theorems on the CEK machine. -/

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

end PlutusCore.UPLC.CekMachine
