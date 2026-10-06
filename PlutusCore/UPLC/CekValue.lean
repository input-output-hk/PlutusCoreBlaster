import PlutusCore.UPLC.Builtins
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekValue

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Builtins

inductive CekValue
| VCon     : Const → CekValue
| VDelay   : Term → List CekValue → CekValue
| VLam     : Term → List CekValue → CekValue
| VConstr  : Nat → List CekValue → CekValue
| VBuiltin : BuiltinFun → List CekValue → ExpectedBuiltinArgs → CekValue
deriving Repr

/-- Positional environment for de Bruijn terms: the head is the value of
    index 0 (the innermost binder), so `ρ[i]?` is de Bruijn lookup. -/
abbrev Environment := List CekValue

end PlutusCore.UPLC.CekValue
