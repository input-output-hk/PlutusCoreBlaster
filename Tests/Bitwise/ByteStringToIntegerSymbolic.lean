import PlutusCore.UPLC
import Blaster

/-! The `ByteStringToInteger` builtin over a symbolic bytestring.

Before `byteStringToIntegerOpaque`, a goal that needed the builtin's value failed to
translate, with "Inductive datatype with instance parameters not supported: `BitVec":
`bstoi_be_loop` folds `Char.toNat` over the `List Char`, and `Char`'s `UInt32` is a
`BitVec` (Lean-blaster #153). The alias makes the builtin an uninterpreted function of the
whole string, as the hash builtins are, so the goals below translate. -/

namespace Tests.Bitwise.ByteStringToIntegerSymbolic
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term Const)
open PlutusCore.UPLC.CekMachine (State)
open PlutusCore.UPLC.CekValue (CekValue)

-- `(lam a [byteStringToInteger True a])`
#import_uplc bstoiSymbolicOneScript PlutusV3 textual "Tests/Bitwise/bstoi_one.uplc"
-- `(lam a (lam b [equalsInteger [byteStringToInteger True a] [byteStringToInteger True b]]))`
#import_uplc bstoiSymbolicTwoScript PlutusV3 textual "Tests/Bitwise/bstoi_two.uplc"

def oneArg (a : ByteString) : List Term := [Term.Const (Const.ByteString a)]
def twoArgs (a b : ByteString) : List Term :=
  [Term.Const (Const.ByteString a), Term.Const (Const.ByteString b)]

#prep_uplc bstoiSymbolicOne bstoiSymbolicOneScript oneArg 200
#prep_uplc bstoiSymbolicTwo bstoiSymbolicTwoScript twoArgs 200

/-- The builtin's value isn't fixed: some bytestring converts to 258 (`#0102`). Needs the
    builtin's value in the solver, so it failed on `BitVec` before the alias. -/
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : ByteString),
    bstoiSymbolicOne.prop a ≠ State.Halt (CekValue.VCon (Const.Integer 258))]

/-- Equal bytestrings convert to equal integers. -/
theorem bstoi_equal_inputs : ∀ (a b : ByteString), a = b →
    bstoiSymbolicTwo.prop a b = State.Halt (CekValue.VCon (Const.Bool true)) := by blaster

/-- And unequal ones aren't known to convert to unequal integers: the function is uninterpreted,
    so only what holds for any function of the string can be proved. -/
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a b : ByteString), a ≠ b →
    bstoiSymbolicTwo.prop a b = State.Halt (CekValue.VCon (Const.Bool false))]

end Tests.Bitwise.ByteStringToIntegerSymbolic
