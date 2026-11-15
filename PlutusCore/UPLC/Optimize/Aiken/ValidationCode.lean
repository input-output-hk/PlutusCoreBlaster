import PlutusCore.UPLC.CekMachine

/-! The unmodified validation body extracted from Aiken v1.1.24's compiled
    eager_beneficiary_signed fixture. No Aiken source-level name is matched.
    See experiments/aiken-validation for the compiler output and provenance. -/
namespace PlutusCore.UPLC.Optimize.Aiken
open PlutusCore.UPLC.Term

/-- List-validation loop body (local parser node 138, beneath two lambdas). -/
def validationBody : Term := (.Force (.Case (.Constr 0 [(.Var 0), (.Delay (.Const (.ConstDataList []))), (.Delay (.Apply (.Lam (.Force (.Case (.Constr 0 [(.Apply (.Apply (.Builtin .EqualsInteger) (.Const (.Integer 28))) (.Apply (.Builtin .LengthOfByteString) (.Var 0))), (.Delay (.Apply (.Apply (.Var 15) (.Apply (.Builtin .BData) (.Var 0))) (.Apply (.Apply (.Var 2) (.Var 2)) (.Apply (.Var 17) (.Var 1))))), (.Delay .Error)]) [(.Var 11)]))) (.Apply (.Builtin .UnBData) (.Apply (.Var 15) (.Var 0)))))]) [(.Var 13)]))

end PlutusCore.UPLC.Optimize.Aiken
