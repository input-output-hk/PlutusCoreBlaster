import PlutusCore.Data.Basic

namespace PlutusCore.Data
open PlutusCore.ByteString (ByteString)
open PlutusCore.Integer (Integer)

/-! ## Theorems on Data representation and builtin functions. -/

@[simp] theorem Data.beq_iff_eq (x y : Data) : x == y ↔ x = y := by
  simp [BEq.beq]
  apply Iff.intro
  . apply eqData_true_imp_eq
  . intro h
    rw [h]
    apply eqData_reflexive

@[simp] theorem Data.not_beq_iff_not_eq (x y : Data) : x != y ↔ x ≠ y := by simp

@[simp] theorem chooseData_constr
  (idx : Integer) (xs : List Data) (tc : α) (tm : α) (tl : α) (ti : α) (tb : α) :
  UPLC.chooseData (Data.Constr idx xs) tc tm tl ti tb = tc := rfl

@[simp] theorem chooseData_map
  (xs : List (Data × Data)) (tc : α) (tm : α) (tl : α) (ti : α) (tb : α) :
  UPLC.chooseData (Data.Map xs) tc tm tl ti tb = tm := rfl

@[simp] theorem chooseData_list
  (xs : List Data) (tc : α) (tm : α) (tl : α) (ti : α) (tb : α) :
  UPLC.chooseData (Data.List xs) tc tm tl ti tb = tl := rfl

@[simp] theorem chooseData_i
  (i : Integer) (tc : α) (tm : α) (tl : α) (ti : α) (tb : α) :
  UPLC.chooseData (Data.I i) tc tm tl ti tb = ti := rfl

@[simp] theorem chooseData_b
  (bs : ByteString) (tc : α) (tm : α) (tl : α) (ti : α) (tb : α) :
  UPLC.chooseData (Data.B bs) tc tm tl ti tb = tb := rfl


@[simp] theorem caseData_constr
  (idx : Integer) (xs : List Data)
  (fc : Integer → List Data → α) (fm : List (Data × Data) → α)
  (fl : List Data → α) (fi : Integer → α) (fb : ByteString → α) :
  UPLC.caseData fc fm fl fi fb (Data.Constr idx xs) = fc idx xs := rfl

@[simp] theorem caseData_map
  (xs : List (Data × Data))
  (fc : Integer → List Data → α) (fm : List (Data × Data) → α)
  (fl : List Data → α) (fi : Integer → α) (fb : ByteString → α) :
  UPLC.caseData fc fm fl fi fb (Data.Map xs) = fm xs := rfl

@[simp] theorem caseData_list
  (xs : List Data)
  (fc : Integer → List Data → α) (fm : List (Data × Data) → α)
  (fl : List Data → α) (fi : Integer → α) (fb : ByteString → α) :
  UPLC.caseData fc fm fl fi fb (Data.List xs) = fl xs := rfl

@[simp] theorem caseData_i
  (i : Integer)
  (fc : Integer → List Data → α) (fm : List (Data × Data) → α)
  (fl : List Data → α) (fi : Integer → α) (fb : ByteString → α) :
  UPLC.caseData fc fm fl fi fb (Data.I i) = fi i := rfl

@[simp] theorem caseData_b
  (bs : ByteString)
  (fc : Integer → List Data → α) (fm : List (Data × Data) → α)
  (fl : List Data → α) (fi : Integer → α) (fb : ByteString → α) :
  UPLC.caseData fc fm fl fi fb (Data.B bs) = fb bs := rfl

@[simp] theorem constrData_rfl (idx : Integer) (xs : List Data) : constrData idx xs = Data.Constr idx xs := rfl
@[simp] theorem mapData_rfl (xs : List (Data × Data)) : mapData xs = Data.Map xs := rfl
@[simp] theorem listData_rfl (xs : List Data) : listData xs = Data.List xs := rfl
@[simp] theorem iData_rfl (i : Integer) : iData i = Data.I i:= rfl
@[simp] theorem bData_rfl (bs : ByteString) : bData bs = Data.B bs:= rfl

@[simp] theorem unConstrData_rfl (idx : Integer) (xs : List Data) :
  unConstrData (Data.Constr idx xs) = pure (idx, xs) := rfl
@[simp] theorem unConstrData_map_eq_err (xs : List (Data × Data)) :
  unConstrData (Data.Map xs) = throw "unConstrData: not a Constr" := rfl
@[simp] theorem unConstrData_list_eq_err (xs : List Data) :
  unConstrData (Data.List xs) = throw "unConstrData: not a Constr" := rfl
@[simp] theorem unConstrData_i_eq_err (i : Integer) :
  unConstrData (Data.I i) = throw "unConstrData: not a Constr" := rfl
@[simp] theorem unConstrData_b_eq_err (bs : ByteString) :
  unConstrData (Data.B bs) = throw "unConstrData: not a Constr" := rfl

@[simp] theorem unMapData_rfl (xs : List (Data × Data)) :
  unMapData (Data.Map xs) = pure xs := rfl
@[simp] theorem unMapData_constr_eq_err (idx : Integer) (xs : List Data) :
  unMapData (Data.Constr idx xs) = throw "unMapData: not a Map" := rfl
@[simp] theorem unMapData_list_eq_err (xs : List Data) :
  unMapData (Data.List xs) = throw "unMapData: not a Map" := rfl
@[simp] theorem unMapData_i_eq_err (i : Integer) :
  unMapData (Data.I i) = throw "unMapData: not a Map" := rfl
@[simp] theorem unMapData_b_eq_err (bs : ByteString) :
  unMapData (Data.B bs) = throw "unMapData: not a Map" := rfl

@[simp] theorem unListData_rfl (xs : List Data) :
  unListData (Data.List xs) = pure xs := rfl
@[simp] theorem unListData_constr_eq_err (idx : Integer) (xs : List Data) :
  unListData (Data.Constr idx xs) = throw "unListData: not a List" := rfl
@[simp] theorem unListData_map_eq_err (xs : List (Data × Data)) :
  unListData (Data.Map xs) = throw "unListData: not a List" := rfl
@[simp] theorem unListData_i_eq_err (i : Integer) :
  unListData (Data.I i) = throw "unListData: not a List" := rfl
@[simp] theorem unListData_b_eq_err (bs : ByteString) :
  unListData (Data.B bs) = throw "unListData: not a List" := rfl

@[simp] theorem unIData_rfl (i : Integer) :
  unIData (Data.I i) = pure i := rfl
@[simp] theorem unIData_constr_eq_err (idx : Integer) (xs : List Data) :
  unIData (Data.Constr idx xs) = throw "unIData: not an I" := rfl
@[simp] theorem unIData_map_eq_err (xs : List (Data × Data)) :
  unIData (Data.Map xs) = throw "unIData: not an I" := rfl
@[simp] theorem unIData_list_eq_err (xs : List Data) :
  unIData (Data.List xs) = throw "unIData: not an I" := rfl
@[simp] theorem unIData_b_eq_err (bs : ByteString) :
  unIData (Data.B bs) = throw "unIData: not an I" := rfl

@[simp] theorem unBData_rfl (bs : ByteString) :
  unBData (Data.B bs) = pure bs := rfl
@[simp] theorem unBData_constr_eq_err (idx : Integer) (xs : List Data) :
  unBData (Data.Constr idx xs) = throw "unBData: not a B" := rfl
@[simp] theorem unBData_map_eq_err (xs : List (Data × Data)) :
  unBData (Data.Map xs) = throw "unBData: not a B" := rfl
@[simp] theorem unBData_list_eq_err (xs : List Data) :
  unBData (Data.List xs) = throw "unBData: not a B" := rfl
@[simp] theorem unBData_i_eq_err (i : Integer) :
  unBData (Data.I i) = throw "unBData: not a B" := rfl

@[simp] theorem equalsData_rfl (d1 d2 : Data) : equalsData d1 d2 = (d1 == d2) := rfl
@[simp] theorem mkPairData_rfl (d1 d2 : Data) : mkPairData d1 d2 = (d1, d2) := rfl
@[simp] theorem mkNilData_rfl (u : Unit) : mkNilData u = [] := rfl
@[simp] theorem mkNilPairData_rfl (u : Unit) : mkNilPairData u = [] := rfl

end PlutusCore.Data
