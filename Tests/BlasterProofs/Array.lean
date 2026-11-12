import Blaster
import PlutusCore.UPLC
import PlutusCore.UPLC.CekMachine

/-! # Array builtins under Blaster

Blaster ports of the Plutus 1.64.0.0 conformance tests for the array builtins and
constants. A success case pins down the exact result where the conformance suite
does (its `programsEvalEquiv` check); a failure case must end in `State.Error`,
not just fail to halt. -/

namespace Tests.BlasterProofs.Array

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Utils (isSuccessful isErrorState)

set_option warn.sorry false

/-- The program version of the conformance tests, `(program 1.1.0 …)`. -/
def version110 : Version := ⟨1, 1, 0⟩

def apply2 (f x y : Term) : Term := .Apply (.Apply f x) y

/-! ## indexArray -/

-- indexArray-01: taking an array element by index.
def indexArray1 : Term :=
  apply2
    (.Force (.Builtin .IndexArray))
    (.Const (.ConstArray [.Integer 1, .Integer 2, .Integer 3, .Integer 4, .Integer 5]))
    (.Const (.Integer 1))

example : isSuccessful (cekExecuteProgram ⟨version110, indexArray1⟩ [] 1000) := by blaster
example : cekExecuteProgram ⟨version110, indexArray1⟩ [] 1000 = .Halt (.VCon (.Integer 2)) := by blaster

-- indexArray-02: taking an array element by an index which is out of bounds.
def indexArray2 : Term :=
  apply2
    (.Force (.Builtin .IndexArray))
    (.Const (.ConstArray [.Integer 1, .Integer 2, .Integer 3, .Integer 4, .Integer 5]))
    (.Const (.Integer 5))

example : isErrorState (cekExecuteProgram ⟨version110, indexArray2⟩ [] 1000) := by blaster

-- indexArray-03: taking an array element by a negative index.
def indexArray3 : Term :=
  apply2
    (.Force (.Builtin .IndexArray))
    (.Const (.ConstArray [.Integer 1, .Integer 2, .Integer 3, .Integer 4, .Integer 5]))
    (.Const (.Integer (-1)))

example : isErrorState (cekExecuteProgram ⟨version110, indexArray3⟩ [] 1000) := by blaster

/-! ## lengthOfArray -/

-- lengthOfArray-01: measuring the length of an empty array.
def lengthOfArray1 : Term :=
  .Apply
    (.Force (.Builtin .LengthOfArray))
    (.Const (.ConstArray []))

example : isSuccessful (cekExecuteProgram ⟨version110, lengthOfArray1⟩ [] 1000) := by blaster
example : cekExecuteProgram ⟨version110, lengthOfArray1⟩ [] 1000 = .Halt (.VCon (.Integer 0)) := by blaster

-- lengthOfArray-02: measuring the length of a non-empty array.
def lengthOfArray2 : Term :=
  .Apply
    (.Force (.Builtin .LengthOfArray))
    (.Const (.ConstArray [.Bool true, .Bool false, .Bool true]))

example : cekExecuteProgram ⟨version110, lengthOfArray2⟩ [] 1000 = .Halt (.VCon (.Integer 3)) := by blaster

/-! ## listToArray

Since the model represents both lists and arrays as `List Const`, the result is
the same element sequence tagged with `ConstArray`. -/

-- listToArray-01: convert an empty list to an array.
def listToArray1 : Term :=
  .Apply
    (.Force (.Builtin .ListToArray))
    (.Const (.ConstList []))

example : cekExecuteProgram ⟨version110, listToArray1⟩ [] 1000 = .Halt (.VCon (.ConstArray [])) := by blaster

-- listToArray-02: convert a non-empty list to an array.
def listToArray2 : Term :=
  .Apply
    (.Force (.Builtin .ListToArray))
    (.Const (.ConstList
      [.Integer 11, .Integer 22, .Integer 33, .Integer 44, .Integer 55,
       .Integer 66, .Integer 77, .Integer 88, .Integer 99]))

example : isSuccessful (cekExecuteProgram ⟨version110, listToArray2⟩ [] 1000) := by blaster

/-! ## Constant arrays

An array constant evaluates to itself. The `illTypedArray-*` conformance cases
are parse errors, not CEK results, so they have no counterpart here. -/

-- emptyArray: (con (array integer) []).
def emptyArray : Term := .Const (.ConstArray [])

example : cekExecuteProgram ⟨version110, emptyArray⟩ [] 1000 = .Halt (.VCon (.ConstArray [])) := by blaster

-- simpleArray: (con (array bool) [True, False, True]).
def simpleArray : Term := .Const (.ConstArray [.Bool true, .Bool false, .Bool true])

example : cekExecuteProgram ⟨version110, simpleArray⟩ [] 1000 = .Halt (.VCon (.ConstArray [.Bool true, .Bool false, .Bool true])) := by blaster

-- unitArray: (con (array unit) [(), (), (), (), ()]).
def unitArray : Term := .Const (.ConstArray [.Unit, .Unit, .Unit, .Unit, .Unit])

example : cekExecuteProgram ⟨version110, unitArray⟩ [] 1000 = .Halt (.VCon (.ConstArray [.Unit, .Unit, .Unit, .Unit, .Unit])) := by blaster

end Tests.BlasterProofs.Array
