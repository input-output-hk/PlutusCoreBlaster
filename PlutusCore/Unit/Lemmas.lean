import PlutusCore.Unit.Basic

namespace PlutusCore.Unit

/-! ## Theorems on PlutusCore Unit representation and builtin functions. -/

@[simp] theorem chooseUnit_rfl (u : Unit) (a : α) : chooseUnit u a = a := rfl

end PlutusCore.Unit
