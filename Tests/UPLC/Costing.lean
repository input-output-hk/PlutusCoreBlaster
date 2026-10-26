import PlutusCore.UPLC.CostModels
import Blaster

open PlutusCore.UPLC.CostModels

example : integerSize 0 = 1 := by decide
#blaster [integerSize 1001 = 1]
#blaster [dataSize (.I 1001) = 5]
#blaster [minArgSize [.VCon (.Data (.I 1001)), .VCon (.Data (.I 1001))] = 5]

-- Both optional lookups preserve the previous proof-indexed definitions.
example (args : List PlutusCore.UPLC.CekValue.CekValue) (i : Nat) :
    argSize args i = (if h : i < args.length then cekValueSize (args.get ⟨i, h⟩) else 1) := by
  unfold argSize
  by_cases h : i < args.length
  · simp [h, List.get_eq_getElem]
  · simp [h]

example (args : List PlutusCore.UPLC.CekValue.CekValue) (i : Nat) :
    argListLen args i = (if h : i < args.length then
      match args.get ⟨i, h⟩ with
      | .VCon (.ConstList cs) => cs.length
      | _ => 0
    else 0) := by
  unfold argListLen
  by_cases h : i < args.length
  · simp only [dif_pos h, List.get_eq_getElem]
    cases args[i] <;> try rfl
  · simp [h]

#blaster [∀ n : Int, argSize [.VCon (.Integer n)] 0 = integerSize n]
#blaster [∀ n : Int, minArgSize [.VCon (.Integer n), .VCon (.Integer 0)] = 1]
