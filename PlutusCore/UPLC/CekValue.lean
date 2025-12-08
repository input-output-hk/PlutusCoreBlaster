import PlutusCore.UPLC.Builtins
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekValue

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Builtins

mutual
  inductive CekValue
  | VCon     : Const → CekValue
  | VDelay   : Term → Environment → CekValue
  | VLam     : String → Term → Environment → CekValue
  | VConstr  : Nat → List CekValue → CekValue
  | VBuiltin : BuiltinFun → List CekValue → ExpectedBuiltinArgs → CekValue
  deriving Repr

  inductive Environment
  | NonEmptyEvironment : Environment → String → CekValue → Environment
  | EmptyEnvironment   : Environment
  deriving Repr
end

end PlutusCore.UPLC.CekValue
