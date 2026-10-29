import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.TextEncoding

/-! # `listToArray` costing

Haskell charges `listToArray` by the spine length of its list argument
(`ExMemoryUsage [a]`), not by the summed size of the elements. Every program
below is `[(force (builtin listToArray)) (con (list t) xs)]`, whose budget is

* CEK startup (100 cpu, 100 mem),
* four steps (apply, force, builtin, const) at 16000 cpu and 100 mem each,
* the builtin: `1000 + 24838 * n` cpu and `7 + n` mem, where `n` is the list length.

The first two cases are the upstream conformance vectors (Plutus 1.64.0.0) and
fix the constant part. Their elements are small integers, which have size 1, so
they cannot tell length from summed size apart. The remaining cases can.
-/

namespace Tests.UPLC.ArrayCosting

open PlutusCore.UPLC.Term (Program)
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.ExBudget (ExBudget)

private def maxBudget : ExBudget :=
  { exBudgetCPU    := { unExCPU    := 10_000_000_000 }
  , exBudgetMemory := { unExMemory := 10_000_000_000 } }

/-- The `(cpu, mem)` spent evaluating `src` as a PlutusV3 program, if it succeeds. -/
private def budgetOf (src : String) : Option (Nat × Nat) :=
  match PlutusCore.UPLC.TextEncoding.programFromString? src with
  | none => none
  | some p =>
    match cekExecuteProgramWithBudget p .plutusV3 .postConway [] maxBudget with
    | .Success _ b => some (b.exBudgetCPU.unExCPU, b.exBudgetMemory.unExMemory)
    | _ => none

-- Upstream `listToArray-01`: the empty list.
#guard budgetOf
  "(program 1.1.0 [ (force (builtin listToArray)) (con (list integer) []) ])"
  == some (65100, 507)

-- Upstream `listToArray-02`: nine small integers.
#guard budgetOf
  "(program 1.1.0 [ (force (builtin listToArray)) (con (list integer) [11,22,33,44,55,66,77,88,99]) ])"
  == some (288642, 516)

-- Three copies of 2^128, each of size 3: charged for 3 elements, not 9.
#guard budgetOf
  "(program 1.1.0 [ (force (builtin listToArray)) (con (list integer) [340282366920938463463374607431768211456, 340282366920938463463374607431768211456, 340282366920938463463374607431768211456]) ])"
  == some (139614, 510)

-- A list of `Data` with a 32-byte bytestring: charged for 2 elements.
#guard budgetOf
  "(program 1.1.0 [ (force (builtin listToArray)) (con (list data) [B #00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff, I 1]) ])"
  == some (114776, 509)

-- A list of `Data` pairs: charged for 1 element.
#guard budgetOf
  "(program 1.1.0 [ (force (builtin listToArray)) (con (list (pair data data)) [(I 340282366920938463463374607431768211456, B #00112233445566778899aabbccddeeff)]) ])"
  == some (89938, 508)

end Tests.UPLC.ArrayCosting
