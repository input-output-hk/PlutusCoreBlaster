import PlutusCore.List.Basic

namespace PlutusCore.List

/-! ## Theorems on PlutusCore List representation and builtin functions. -/

@[simp] theorem chooseList_nil (t1 : β) (t2 : β) : UPLC.chooseList ([] : List α) t1 t2 = t1 := rfl

theorem chooseList_empty (xs : List α) (t1 : β) (t2 : β) :
  List.isEmpty xs → UPLC.chooseList xs t1 t2 = t1 := by
  intro; split
  . rfl
  . contradiction

theorem chooseList_not_empty (xs : List α) (t1 : β) (t2 : β) :
  ¬ List.isEmpty xs → UPLC.chooseList xs t1 t2 = t2 := by
  intro; split
  . contradiction
  . rfl

@[simp] theorem caseList_nil (n : β) (f : α → List α → β) : UPLC.caseList n f [] = n := rfl

theorem caseList_empty (n : β) (f : α → List α → β) (xs : List α) :
  List.isEmpty xs → UPLC.caseList n f xs = n := by
  match xs with
  | [] => simp
  | _ :: _ => simp [List.isEmpty]

@[simp] theorem caseList_not_empty (n : β) (f : α → List α → β) (x : α) (xs : List α) :
        UPLC.caseList n f (x :: xs) = f x xs := by simp

@[simp] theorem mkCons_rfl (x : α) (xs : List α) : mkCons x xs = x :: xs := rfl

end PlutusCore.List
