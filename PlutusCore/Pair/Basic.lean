
namespace PlutusCore.Pair

/-! ## Formalisation for PlutusCore Pair representation and builtin functions. -/

namespace PlutusCore.PairInternal

-- We here use the Lean4 Prod representation

/-! ## Builtin Pair functions. -/

/-- Given pair `(x, y)` return `x` -/
def fstPair (x : α × β) := x.fst

/-- Given pair `(x, y)` return `y` -/
def sndPair (x : α × β) := x.snd

end PlutusCore.PairInternal

export PlutusCore.PairInternal
  ( -- builtin functions
    fstPair
    sndPair
  )

end PlutusCore.Pair

