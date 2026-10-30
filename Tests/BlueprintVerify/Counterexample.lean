import PlutusCore.UPLC.Utils
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

-- Observe a wrapper through ordinary helpers, retaining all exact return data.
namespace ReplayObservation
open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.UPLC.Term

def compiled (x : Int) : PlutusCore.UPLC.CekMachine.State := .Halt (.VCon (.Integer x))
def adapter (x : Int) : PlutusCore.UPLC.CekMachine.State := compiled (x + 1)
def assertion (x : Int) : Prop := adapter x = .Halt (.VCon (.Integer 7))
end ReplayObservation

run_cmd liftTermElabM do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term "ReplayObservation.assertion 6")
  let original ← Term.elabTermAndSynthesize stx (some (mkSort .zero))
  let (observed, calls) ← observe original #[``ReplayObservation.compiled]
  unless calls.size == 1 do throwError "compiled wrapper was not captured"
  unless ← isDefEq observed (← withTransparency .all (whnf original)) do
    throwError "exact returned constant was changed during replay"
  unless ← decideClosed (← mkAppM ``Iff #[mkConst ``False, mkConst ``False]) do
    throwError "closed logical connective replay failed"
  logInfo "PASS wrapper discovery through adapters preserves the exact returned constant"

#guard (toCEX (PlutusCore.Data.Data.B {data := "€"})).error?.isSome
#guard (toCEX (PlutusCore.Data.Data.B {data := String.singleton (Char.ofNat 233)})).error?.isNone

namespace ReplayObservation
-- Exhausted CEK evaluation is not a rejection witness.
def unfinished : PlutusCore.UPLC.CekMachine.State :=
  .Eval [] [] (.Const .Unit)
end ReplayObservation

run_cmd liftTermElabM do
  let e ← mkAppM ``PlutusCore.UPLC.Utils.isUnsuccessful #[mkConst ``ReplayObservation.unfinished]
  let succeeded ← try
    discard <| observe e #[``ReplayObservation.unfinished]
    pure true
  catch _ => pure false
  if succeeded then throwError "unfinished evaluation was accepted as a replay witness"
  logInfo "PASS byte codec refuses truncation and unfinished CEK execution is not rejection"

namespace ReplayObservation
structure SourceInput where
  amount : Int
instance : ToCEX SourceInput := ⟨fun x => .encoded "SourceInput" "example-wire" (toCEX x.amount)⟩
def encode (x : SourceInput) : PlutusCore.Data.Data := .I x.amount
def script (d : PlutusCore.Data.Data) : PlutusCore.UPLC.CekMachine.State :=
  .Halt (.VCon (.Data d))
end ReplayObservation

run_cmd liftTermElabM do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term
    "ReplayObservation.script (ReplayObservation.encode ⟨9⟩)")
  let e ← Term.elabTermAndSynthesize stx none
  let (_, calls) ← observe e #[``ReplayObservation.script]
  let call ← ofExcept (calls[0]!.getObjValAs? (Array Json) "sourceArguments")
  unless call.size == 1 do throwError "direct encoder lost the typed source input"
  let arg ← ofExcept (call[0]!.getObjVal? "argument")
  let value ← ofExcept (arg.getObjVal? "value")
  unless (value.getObjValAs? String "kind").toOption == some "encoded" do
    throwError "direct encoder did not retain the source codec"
  logInfo "PASS direct wire encoders retain typed source inputs without a scenario adapter"
