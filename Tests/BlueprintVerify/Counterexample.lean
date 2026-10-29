import Blaster.Counterexample.Decode
import PlutusCore.UPLC.BlueprintEncoding.Counterexample

open Lean Meta Elab Command
open Blaster.Counterexample
open PlutusCore.UPLC.BlueprintEncoding.Counterexample

run_cmd liftTermElabM do
  let one ← decode `x₀ `x (mkConst ``Int) "1"
  let negative ← decode `x₁ `x (mkConst ``Int) "(- 1)"
  let parseProp : String → TermElabM Expr := fun src => do
    let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term src)
    Term.elabTermAndSynthesize stx (some (mkSort .zero))
  let original ← parseProp "∀ (x : Int), x < 0"
  let cases : List (Model × String) := [
      ({ bindings := #[one] }, "confirmed"),
      ({ bindings := #[negative] }, "not-reproduced"),
      ({}, "unavailable"),
      ({ bindings := #[one, negative] }, "unavailable")]
  for (model, status) in cases do
    let result ← replay original model
    unless (result.getObjValAs? String "status").toOption == some status do
      throwError "incorrect replay outcome: {result}"
  let shadowed ← parseProp "∀ (x : Int), ∀ (x : Int), x < 0"
  let result ← replay shadowed { bindings := #[one] }
  unless (result.getObjValAs? String "status").toOption == some "unavailable" do
    throwError "shadowed original variables received fabricated assignments"
  logInfo "PASS replay confirms genuine witnesses and rejects non-witnesses, missing, ambiguous and shadowed bindings"
