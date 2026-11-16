import PlutusCore.Default
import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.TextEncoding

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/86
--
-- Plutus 1.64 picks the builtin semantics variant from the ledger language and
-- the major protocol version (`machineParametersFor` in `MachineParameters.hs`):
--
--   |        | PV 5–8 | PV 9–10 | PV ≥ 11 |
--   |--------|--------|---------|---------|
--   | V1, V2 | A      | B       | D       |
--   | V3     | (C)    | C       | E       |
--
-- `toSemanticsVariant` used to return D/E at PV 9–10. With #33's `ConstrData`
-- range check (D/E only), that made budgeted execution at PV 9–10 reject
-- constructor indices that 1.64 accepts there.
namespace Tests.Issue86

open PlutusCore.Default (PlutusVersion ProtocolVersion)
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.ExBudget (ExBudget)

/-! ## One check per cell of the table -/

example : PlutusVersion.toSemanticsVariant .plutusV1 .preConway = .defaultFunSemanticsVariantA := rfl
example : PlutusVersion.toSemanticsVariant .plutusV1 .postConwayPreVanRossem = .defaultFunSemanticsVariantB := rfl
example : PlutusVersion.toSemanticsVariant .plutusV1 .postVanRossem = .defaultFunSemanticsVariantD := rfl
example : PlutusVersion.toSemanticsVariant .plutusV2 .preConway = .defaultFunSemanticsVariantA := rfl
example : PlutusVersion.toSemanticsVariant .plutusV2 .postConwayPreVanRossem = .defaultFunSemanticsVariantB := rfl
example : PlutusVersion.toSemanticsVariant .plutusV2 .postVanRossem = .defaultFunSemanticsVariantD := rfl
-- PlutusV3 does not exist before PV 9; 1.64 would still pick C for it there.
example : PlutusVersion.toSemanticsVariant .plutusV3 .preConway = .defaultFunSemanticsVariantC := rfl
example : PlutusVersion.toSemanticsVariant .plutusV3 .postConwayPreVanRossem = .defaultFunSemanticsVariantC := rfl
example : PlutusVersion.toSemanticsVariant .plutusV3 .postVanRossem = .defaultFunSemanticsVariantE := rfl

/-! ## End to end through `cekExecuteProgramWithBudget`

`[(builtin constrData) (con integer i) (con (list data) [])]` for each language
and protocol version. The expected outcomes and budgets are the Plutus 1.64.0.0
`uplc evaluate -c -S <variant>` results for the variant in the table above.
-/

private inductive Outcome
  | success (cpu mem : Nat)
  | evaluationError
  | budgetExhausted
  | parseError
deriving DecidableEq

private def maxBudget : ExBudget :=
  { exBudgetCPU    := { unExCPU    := 10_000_000_000 }
  , exBudgetMemory := { unExMemory := 10_000_000_000 } }

private def constrDataAt (i : String) (lv : PlutusVersion) (pv : ProtocolVersion) : Outcome :=
  let src := s!"(program 1.0.0 [ [ (builtin constrData) (con integer {i}) ] (con (list data) []) ])"
  match PlutusCore.UPLC.TextEncoding.programFromString? src with
  | none => .parseError
  | some p =>
    match cekExecuteProgramWithBudget p lv pv [] maxBudget with
    | .Success _ b => .success b.exBudgetCPU.unExCPU b.exBudgetMemory.unExMemory
    | .EvaluationError => .evaluationError
    | .BudgetExhausted _ => .budgetExhausted

private def outOfRange : List String := ["-1", "18446744073709551616"]
private def inRange : List String := ["0", "18446744073709551615"]
private def allIndices : List String := outOfRange ++ inRange

-- PV 5–8: A for V1/V2, C for V3. Any index is accepted.
#guard allIndices.all fun i =>
  constrDataAt i .plutusV1 .preConway = .success 204241 632 &&
  constrDataAt i .plutusV2 .preConway = .success 204241 632 &&
  constrDataAt i .plutusV3 .preConway = .success 102251 632

-- PV 9–10: B for V1/V2, C for V3. Any index is accepted. This is the cell that
-- returned an evaluation error for out-of-range indices before the fix.
#guard allIndices.all fun i =>
  [PlutusVersion.plutusV1, .plutusV2, .plutusV3].all fun lv =>
    constrDataAt i lv .postConwayPreVanRossem = .success 102251 632

-- PV ≥ 11: D for V1/V2, E for V3. The index must fit in a Word64.
#guard inRange.all fun i =>
  [PlutusVersion.plutusV1, .plutusV2, .plutusV3].all fun lv =>
    constrDataAt i lv .postVanRossem = .success 102251 632
#guard outOfRange.all fun i =>
  [PlutusVersion.plutusV1, .plutusV2, .plutusV3].all fun lv =>
    constrDataAt i lv .postVanRossem = .evaluationError

end Tests.Issue86
