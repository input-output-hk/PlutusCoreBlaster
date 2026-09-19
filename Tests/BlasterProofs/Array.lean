import Blaster
import PlutusCore.UPLC
import PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.TextEncoding

set_option warn.sorry false

def plutusV3 : Version := ⟨1, 1, 0⟩

def isSuccessful : State → Bool
  | .Halt _ => true
  | _       => false

def apply2 (f x y : Term) : Term := .Apply (.Apply f x) y

/-! ## indexArray

Blaster ports of the `builtin/semantics/indexArray` conformance tests. The
success case additionally pins down the exact returned element (mirroring the
conformance suite's `programsEvalEquiv` check), while the out-of-bounds and
negative-index cases must fail to evaluate. -/

-- indexArray-01: taking an array element by index.
def indexArray1 : Term :=
  apply2
    (.Force (.Builtin .IndexArray))
    (.Const (.ConstArray [.Integer 1, .Integer 2, .Integer 3, .Integer 4, .Integer 5]))
    (.Const (.Integer 1))

#blaster [isSuccessful (cekExecuteProgram ⟨plutusV3, indexArray1⟩ [] 1000) = true]
example : isSuccessful (cekExecuteProgram ⟨plutusV3, indexArray1⟩ [] 1000) := by blaster

#blaster [cekExecuteProgram ⟨plutusV3, indexArray1⟩ [] 1000 = .Halt (.VCon (.Integer 2))]
example : cekExecuteProgram ⟨plutusV3, indexArray1⟩ [] 1000 = .Halt (.VCon (.Integer 2)) := by blaster

-- indexArray-02: taking an array element by an index which is out of bounds.
def indexArray2 : Term :=
  apply2
    (.Force (.Builtin .IndexArray))
    (.Const (.ConstArray [.Integer 1, .Integer 2, .Integer 3, .Integer 4, .Integer 5]))
    (.Const (.Integer 5))

#blaster (solve-result: 1) (gen-cex: 0) [isSuccessful (cekExecuteProgram ⟨plutusV3, indexArray2⟩ [] 1000) = true]
example : ¬ isSuccessful (cekExecuteProgram ⟨plutusV3, indexArray2⟩ [] 1000) := by blaster

-- indexArray-03: taking an array element by a negative index.
def indexArray3 : Term :=
  apply2
    (.Force (.Builtin .IndexArray))
    (.Const (.ConstArray [.Integer 1, .Integer 2, .Integer 3, .Integer 4, .Integer 5]))
    (.Const (.Integer (-1)))

#blaster (solve-result: 1) (gen-cex: 0) [isSuccessful (cekExecuteProgram ⟨plutusV3, indexArray3⟩ [] 1000) = true]
example : ¬ isSuccessful (cekExecuteProgram ⟨plutusV3, indexArray3⟩ [] 1000) := by blaster

/-! ## lengthOfArray

Blaster ports of the `builtin/semantics/lengthOfArray` conformance tests. -/

-- lengthOfArray-01: measuring the length of an empty array.
def lengthOfArray1 : Term :=
  .Apply
    (.Force (.Builtin .LengthOfArray))
    (.Const (.ConstArray []))

#blaster [isSuccessful (cekExecuteProgram ⟨plutusV3, lengthOfArray1⟩ [] 1000) = true]
example : isSuccessful (cekExecuteProgram ⟨plutusV3, lengthOfArray1⟩ [] 1000) := by blaster

#blaster [cekExecuteProgram ⟨plutusV3, lengthOfArray1⟩ [] 1000 = .Halt (.VCon (.Integer 0))]
example : cekExecuteProgram ⟨plutusV3, lengthOfArray1⟩ [] 1000 = .Halt (.VCon (.Integer 0)) := by blaster

-- lengthOfArray-02: measuring the length of a non-empty array.
def lengthOfArray2 : Term :=
  .Apply
    (.Force (.Builtin .LengthOfArray))
    (.Const (.ConstArray [.Bool true, .Bool false, .Bool true]))

#blaster [cekExecuteProgram ⟨plutusV3, lengthOfArray2⟩ [] 1000 = .Halt (.VCon (.Integer 3))]
example : cekExecuteProgram ⟨plutusV3, lengthOfArray2⟩ [] 1000 = .Halt (.VCon (.Integer 3)) := by blaster

/-! ## listToArray

Blaster ports of the `builtin/semantics/listToArray` conformance tests. Since
the model represents both lists and arrays as `List Const`, the result is the
same element sequence tagged with `ConstArray`. -/

-- listToArray-01: convert an empty list to an array.
def listToArray1 : Term :=
  .Apply
    (.Force (.Builtin .ListToArray))
    (.Const (.ConstList []))

#blaster [cekExecuteProgram ⟨plutusV3, listToArray1⟩ [] 1000 = .Halt (.VCon (.ConstArray []))]
example : cekExecuteProgram ⟨plutusV3, listToArray1⟩ [] 1000 = .Halt (.VCon (.ConstArray [])) := by blaster

-- listToArray-02: convert a non-empty list to an array.
def listToArray2 : Term :=
  .Apply
    (.Force (.Builtin .ListToArray))
    (.Const (.ConstList
      [.Integer 11, .Integer 22, .Integer 33, .Integer 44, .Integer 55,
       .Integer 66, .Integer 77, .Integer 88, .Integer 99]))

#blaster [isSuccessful (cekExecuteProgram ⟨plutusV3, listToArray2⟩ [] 1000) = true]
example : isSuccessful (cekExecuteProgram ⟨plutusV3, listToArray2⟩ [] 1000) := by blaster

/-! ## Constant arrays

Blaster ports of the `builtin/constant/array` conformance tests: an array
constant evaluates to itself. The `illTypedArray-*` conformance cases are
parser-level failures (`parse error`), not CEK evaluation results, so they have
no counterpart here. -/

-- emptyArray: (con (array integer) []).
def emptyArray : Term := .Const (.ConstArray [])

#blaster [cekExecuteProgram ⟨plutusV3, emptyArray⟩ [] 1000 = .Halt (.VCon (.ConstArray []))]
example : cekExecuteProgram ⟨plutusV3, emptyArray⟩ [] 1000 = .Halt (.VCon (.ConstArray [])) := by blaster

-- simpleArray: (con (array bool) [True, False, True]).
def simpleArray : Term := .Const (.ConstArray [.Bool true, .Bool false, .Bool true])

#blaster [cekExecuteProgram ⟨plutusV3, simpleArray⟩ [] 1000 = .Halt (.VCon (.ConstArray [.Bool true, .Bool false, .Bool true]))]
example : cekExecuteProgram ⟨plutusV3, simpleArray⟩ [] 1000 = .Halt (.VCon (.ConstArray [.Bool true, .Bool false, .Bool true])) := by blaster

-- unitArray: (con (array unit) [(), (), (), (), ()]).
def unitArray : Term := .Const (.ConstArray [.Unit, .Unit, .Unit, .Unit, .Unit])

#blaster [cekExecuteProgram ⟨plutusV3, unitArray⟩ [] 1000 = .Halt (.VCon (.ConstArray [.Unit, .Unit, .Unit, .Unit, .Unit]))]
example : cekExecuteProgram ⟨plutusV3, unitArray⟩ [] 1000 = .Halt (.VCon (.ConstArray [.Unit, .Unit, .Unit, .Unit, .Unit])) := by blaster
