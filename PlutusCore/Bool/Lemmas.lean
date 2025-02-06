import PlutusCore.Bool.Basic

namespace PlutusCore.Bool

/-! ## Theorems on Bool representation and builtin functions. -/

@[simp] theorem ifThenElse_rfl (b : Bool) (t : α) (e : α) : ifThenElse b t e = if b then t else e := rfl

end PlutusCore.Bool
