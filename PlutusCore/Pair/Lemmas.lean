import PlutusCore.Pair.Basic

namespace PlutusCore.Pair

/-! ## Theorems on PlutusCore Pair representation and builtin functions. -/

@[simp] theorem fstPair_rfl (x : α × β) : fstPair x = x.fst := rfl
@[simp] theorem sndPair_rfl (x : α × β) : sndPair x = x.snd := rfl

end PlutusCore.Pair
