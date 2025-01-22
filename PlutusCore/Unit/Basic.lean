
namespace PlutusCore.Unit

/-! ## Formalisation for PlutusCore Unit representation and builtin functions. -/

-- We here use the Lean4 Unit representation

/-! ## Builtin Unit functions. -/

/-- Given `u` and `a` always return `a`. -/
def chooseUnit (_u : Unit) (a : α) : α := a

end PlutusCore.Unit
