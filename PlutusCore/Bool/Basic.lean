
namespace PlutusCore.Bool

/-! ## Formalisation for PlutusCore Bool representation and builtin functions. -/

namespace PlutusCore.BoolInternal

-- We here use the Lean4 Bool representation

/-! ## Builtin Bool functions. -/

/-- Given `u` and `a` always return `a`. -/
def ifThenElse (b : Bool) (t : α) (e : α) : α := if b then t else e

end PlutusCore.BoolInternal

export PlutusCore.BoolInternal
  ( -- builtin function
    ifThenElse
  )

end PlutusCore.Bool
