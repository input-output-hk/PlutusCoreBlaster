import PlutusCore.Data.Basic

namespace PlutusCore.Data

/-! These examples fail unless `eqData` and `ltData` compile by structural recursion. -/

example : Data.I 1 = Data.I 1 := by decide
example : Data.Constr 0 [Data.List [Data.I 1]] ≠ Data.Constr 0 [Data.List [Data.I 2]] := by decide
example : Data.Map [(Data.I 1, Data.I 2), (Data.I 3, Data.I 4)]
    = Data.Map [(Data.I 1, Data.I 2), (Data.I 3, Data.I 4)] := by decide
example : Data.List [Data.I 1] ≠ Data.List [Data.I 1, Data.I 2] := by decide
example : Data.Constr 0 [Data.I 1] < Data.Constr 1 [Data.I 2] := by decide
example : ¬ (Data.I 2 < Data.I 1) := by decide

example (i i' : PlutusCore.Integer.Integer) (a a' : List Data) :
    ((i == i') && eqDataList a a') = eqData (.Constr i a) (.Constr i' a') := by simp [eqData]

example (i i' : PlutusCore.Integer.Integer) (a a' : List Data) :
    (i < i' && ltDataList a a') = ltData (.Constr i a) (.Constr i' a') := by simp [ltData]

end PlutusCore.Data
