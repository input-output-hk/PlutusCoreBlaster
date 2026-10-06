import PlutusCore.UPLC.CekMachine

/-! ## Decidable equality for the CEK machine types

`CekValue` nests `List CekValue`, so its `BEq` is a hand-written structural recursion, which
`decide` reduces. -/

namespace PlutusCore.UPLC.CekValue

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Builtins

mutual
  def eqCekValue : CekValue → CekValue → Bool
    | .VCon a, .VCon b => a == b
    | .VDelay t1 e1, .VDelay t2 e2 => t1 == t2 && eqCekValueList e1 e2
    | .VLam t1 e1, .VLam t2 e2 => t1 == t2 && eqCekValueList e1 e2
    | .VConstr i a, .VConstr j b => i == j && eqCekValueList a b
    | .VBuiltin f1 a1 s1, .VBuiltin f2 a2 s2 => f1 == f2 && eqCekValueList a1 a2 && s1 == s2
    | _, _ => false

  def eqCekValueList : List CekValue → List CekValue → Bool
    | [], [] => true
    | a :: as, b :: bs => eqCekValue a b && eqCekValueList as bs
    | _, _ => false
end

instance instBEqCekValue : BEq CekValue := ⟨eqCekValue⟩

mutual
  theorem eqCekValue_true_imp_eq : ∀ a b : CekValue, eqCekValue a b = true → a = b := by
    intro a b h
    cases a <;> cases b <;> simp_all [eqCekValue]
    case VDelay.VDelay | VLam.VLam | VConstr.VConstr => exact eqCekValueList_true_imp_eq _ _ h.2
    case VBuiltin.VBuiltin => exact eqCekValueList_true_imp_eq _ _ h.1.2

  theorem eqCekValueList_true_imp_eq :
      ∀ a b : List CekValue, eqCekValueList a b = true → a = b := by
    intro a b h
    cases a <;> cases b <;> simp_all [eqCekValueList]
    case cons.cons => exact ⟨eqCekValue_true_imp_eq _ _ h.1, eqCekValueList_true_imp_eq _ _ h.2⟩
end

mutual
  theorem eqCekValue_reflexive : ∀ a : CekValue, eqCekValue a a = true := by
    intro a
    cases a <;> simp [eqCekValue]
    case VDelay | VLam | VConstr | VBuiltin => exact eqCekValueList_reflexive _

  theorem eqCekValueList_reflexive : ∀ a : List CekValue, eqCekValueList a a = true := by
    intro a
    cases a <;> simp [eqCekValueList]
    case cons => exact ⟨eqCekValue_reflexive _, eqCekValueList_reflexive _⟩
end

instance : LawfulBEq CekValue where
  eq_of_beq {a b} := eqCekValue_true_imp_eq a b
  rfl {a} := eqCekValue_reflexive a

instance : DecidableEq CekValue := instDecidableEqOfLawfulBEq

end PlutusCore.UPLC.CekValue

namespace PlutusCore.UPLC.CekMachine

deriving instance DecidableEq for Frame
deriving instance DecidableEq for State
deriving instance DecidableEq for EvaluationResult

end PlutusCore.UPLC.CekMachine
