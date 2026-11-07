import PlutusCore.UPLC
import Blaster

/-! The `ByteStringToInteger` builtin over a symbolic bytestring.

The builtin reads its bytes through `PlutusCore.Bytes` (see `PlutusCore/ByteString/Bytes.lean`), so
Blaster translates it as defined, through the CEK machine's dispatch. A goal that needs the value
it computes takes `PlutusCore.Bytes.Spec` as a premise, which `PlutusCore.Bytes.spec` proves.

The builtin used to go through an `opaque` alias, which the solver saw as some function of the
whole string with a non-negative result. Now that the definition is visible, non-negativity
follows from it only by induction over the length of the string, which the solver does not do;
the two theorems that say so are proved in Lean instead.

The `blaster` goals need the solver that CI builds. Each has a timeout. -/

namespace Tests.Bitwise.ByteStringToIntegerSymbolic
open PlutusCore.ByteString (ByteString)
open PlutusCore.Bytes (Spec byteStr)
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

/-- The run halts with the integer `n`. -/
def haltsWithInteger (s : State) (n : Int) : Prop :=
  s = .Halt (.VCon (.Integer n))

/-- The run halts with the boolean `b`. -/
def haltsWithBool (s : State) (b : Bool) : Prop :=
  s = .Halt (.VCon (.Bool b))

-- Some bytestring converts to 258 (`#0102`).
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 60) [∀ (a : ByteString),
    ¬ haltsWithInteger (bstoiSymbolicOne.prop a) 258]

/-- With `Spec`, the value is the one the bytes give. -/
theorem bstoi_two_bytes : Spec → ∀ (x y : Nat), x < 256 → y < 256 →
    haltsWithInteger (bstoiSymbolicOne.prop ⟨byteStr x ++ byteStr y⟩) (256 * x + y) := by
  blaster (timeout: 60)

/-- The result is never negative. -/
theorem bstoi_nonnegative : ∀ (a : ByteString) (n : Int),
    haltsWithInteger (bstoiSymbolicOne.prop a) n → 0 ≤ n := by
  intro a n h
  have hp : bstoiSymbolicOne.prop a =
      .Halt (.VCon (.Integer (PlutusCore.Bitwise.byteStringToInteger true a.data))) := rfl
  rw [haltsWithInteger, hp] at h
  cases h
  exact Int.natCast_nonneg _

/-- Equal bytestrings convert to equal integers. -/
theorem bstoi_equal_inputs : ∀ (a b : ByteString), a = b →
    haltsWithBool (bstoiSymbolicTwo.prop a b) true := by blaster

-- Unequal ones need not convert to unequal integers: a leading zero byte adds nothing (`#01` and
-- `#0001` are both 1).
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 60) [∀ (a b : ByteString), a ≠ b →
    haltsWithBool (bstoiSymbolicTwo.prop a b) false]

-- The same goals over `cekExecuteProgram` itself, with no `#prep_uplc`: Blaster unfolds the
-- CEK machine's own dispatch down to the byte loop.
#blaster (gen-cex: 0) (solve-result: 1) (timeout: 60) [∀ (a : ByteString),
    ¬ haltsWithInteger (cekExecuteProgram bstoiSymbolicOneScript.script (oneArg a) 200) 258]

theorem bstoi_two_bytes_cek : Spec → ∀ (x y : Nat), x < 256 → y < 256 →
    haltsWithInteger
      (cekExecuteProgram bstoiSymbolicOneScript.script (oneArg ⟨byteStr x ++ byteStr y⟩) 200)
      (256 * x + y) := by
  blaster (timeout: 60)

theorem bstoi_nonnegative_cek : ∀ (a : ByteString) (n : Int),
    haltsWithInteger (cekExecuteProgram bstoiSymbolicOneScript.script (oneArg a) 200) n → 0 ≤ n := by
  intro a n h
  have hp : cekExecuteProgram bstoiSymbolicOneScript.script (oneArg a) 200 =
      .Halt (.VCon (.Integer (PlutusCore.Bitwise.byteStringToInteger true a.data))) := by
    with_unfolding_all rfl
  rw [haltsWithInteger, hp] at h
  cases h
  exact Int.natCast_nonneg _

theorem bstoi_equal_inputs_cek : ∀ (a b : ByteString), a = b →
    haltsWithBool (cekExecuteProgram bstoiSymbolicTwoScript.script (twoArgs a b) 200) true := by
  blaster

-- Compiled evaluation: `#0102` is 258.
#guard match cekExecuteProgram bstoiSymbolicOneScript.script (oneArg ⟨"\x01\x02"⟩) 200 with
  | .Halt (.VCon (.Integer n)) => n == 258
  | _ => false

end Tests.Bitwise.ByteStringToIntegerSymbolic
