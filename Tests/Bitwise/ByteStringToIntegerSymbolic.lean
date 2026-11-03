import PlutusCore.UPLC
import Blaster

/-! The `ByteStringToInteger` builtin over a symbolic bytestring.

Before `byteStringToIntegerOpaque`, a goal that needed the builtin's value failed to
translate, with "Inductive datatype with instance parameters not supported: `BitVec":
`bstoi_be_loop` folds `Char.toNat` over the `List Char`, and `Char`'s `UInt32` is a
`BitVec` (Lean-blaster #153). The alias makes the builtin an uninterpreted function of the
whole string, as the hash builtins are, so the goals below translate. It returns a `Nat`, so
the builtin's result is still known to be non-negative. -/

namespace Tests.Bitwise.ByteStringToIntegerSymbolic
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term Const)
open PlutusCore.UPLC.CekMachine (State cekExecuteProgram)

-- `(lam a [byteStringToInteger True a])`
#import_uplc bstoiSymbolicOneScript PlutusV3 textual "Tests/Bitwise/bstoi_one.uplc"
-- `(lam a (lam b [equalsInteger [byteStringToInteger True a] [byteStringToInteger True b]]))`
#import_uplc bstoiSymbolicTwoScript PlutusV3 textual "Tests/Bitwise/bstoi_two.uplc"

def oneArg (a : ByteString) : List Term := [Term.Const (Const.ByteString a)]
def twoArgs (a b : ByteString) : List Term :=
  [Term.Const (Const.ByteString a), Term.Const (Const.ByteString b)]

#prep_uplc bstoiSymbolicOne bstoiSymbolicOneScript oneArg 200
#prep_uplc bstoiSymbolicTwo bstoiSymbolicTwoScript twoArgs 200

/-- The run halts with the integer `n`. A match, as `Tests/BlueprintVerify/BooleanCase.lean`'s
    predicates are, so the solver sees the result and never the whole CEK datatype: its
    `Const` holds BLS12-381 points, whose `Fq1.t : Fin fieldPrime` Blaster can't declare. -/
def haltsWithInteger (s : State) (n : Int) : Prop :=
  match s with
  | .Halt (.VCon (.Integer m)) => m = n
  | _ => False

/-- The run halts with the boolean `b`. -/
def haltsWithBool (s : State) (b : Bool) : Prop :=
  match s with
  | .Halt (.VCon (.Bool c)) => c = b
  | _ => False

-- The builtin's value isn't fixed: some bytestring converts to 258 (`#0102`). Needs the
-- builtin's value in the solver, so it failed on `BitVec` before the alias.
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : ByteString),
    ¬ haltsWithInteger (bstoiSymbolicOne.prop a) 258]

/-- But it's never negative: the alias returns a `Nat`. -/
theorem bstoi_nonnegative : ∀ (a : ByteString) (n : Int),
    haltsWithInteger (bstoiSymbolicOne.prop a) n → 0 ≤ n := by blaster

/-- Equal bytestrings convert to equal integers. -/
theorem bstoi_equal_inputs : ∀ (a b : ByteString), a = b →
    haltsWithBool (bstoiSymbolicTwo.prop a b) true := by blaster

-- And unequal ones aren't known to convert to unequal integers: the function is uninterpreted,
-- so only what holds for any function of the string can be proved.
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a b : ByteString), a ≠ b →
    haltsWithBool (bstoiSymbolicTwo.prop a b) false]

-- The same goals over `cekExecuteProgram` itself, with no `#prep_uplc`: Blaster unfolds the
-- CEK machine's own dispatch down to the alias.
#blaster (gen-cex: 0) (solve-result: 1) [∀ (a : ByteString),
    ¬ haltsWithInteger (cekExecuteProgram bstoiSymbolicOneScript.script (oneArg a) 200) 258]

theorem bstoi_nonnegative_cek : ∀ (a : ByteString) (n : Int),
    haltsWithInteger (cekExecuteProgram bstoiSymbolicOneScript.script (oneArg a) 200) n → 0 ≤ n := by
  blaster

theorem bstoi_equal_inputs_cek : ∀ (a b : ByteString), a = b →
    haltsWithBool (cekExecuteProgram bstoiSymbolicTwoScript.script (twoArgs a b) 200) true := by
  blaster

-- Compiled evaluation runs the alias's value, the conversion itself: `#0102` is 258.
#guard match cekExecuteProgram bstoiSymbolicOneScript.script (oneArg ⟨"\x01\x02"⟩) 200 with
  | .Halt (.VCon (.Integer n)) => n == 258
  | _ => false

end Tests.Bitwise.ByteStringToIntegerSymbolic
