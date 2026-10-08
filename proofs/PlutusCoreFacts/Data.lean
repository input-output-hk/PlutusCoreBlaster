import PlutusCore.Data
import Blaster

/-! The Data equality observers agree with propositional equality. -/

namespace PlutusCore.Data

/-- A successful builtin data comparison identifies the compared values. -/
@[blaster_library] theorem eqData_eq_decide (x y : Data) : eqData x y = decide (x = y) := by
  blaster (summaries: [eqData_true_imp_eq x y, eqData_false_imp_not_eq x y])
    (timeout: 5) (gen-cex: 0)

@[blaster_library] theorem eqDataList_eq_decide (xs ys : List Data) :
    eqDataList xs ys = decide (xs = ys) := by
  blaster (summaries: [eqDataList_true_imp_eq xs ys, eqDataList_false_imp_not_eq xs ys])
    (timeout: 5) (gen-cex: 0)

@[blaster_library] theorem eqDataMap_eq_decide (xs ys : List (Data × Data)) :
    eqDataMap xs ys = decide (xs = ys) := by
  blaster (summaries: [eqDataMap_true_imp_eq xs ys, eqDataMap_false_imp_not_eq xs ys])
    (timeout: 5) (gen-cex: 0)

end PlutusCore.Data
