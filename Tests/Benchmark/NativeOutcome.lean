import Benchmark.PrepUplc.Driver.Report

namespace Tests.Benchmark.NativeOutcome

open Lean
open Benchmark.PrepUplc
open Benchmark.PrepUplc.Driver

-- Preserve every published outcome label, including the historical diagnostic.
def wireCases : List (NativeOutcome × String) :=
  [(.halted, "halt"), (.failed, "error"), (.exhausted, "exhausted"), (.running, "running")]

#guard wireCases.all fun (outcome, label) =>
  toJson outcome == Json.str label &&
    (fromJson? (Json.str label) : Except String NativeOutcome).toOption == some outcome

#guard (fromJson? (Json.str "exhaused") : Except String NativeOutcome).toOption.isNone
#guard (fromJson? (toJson (42 : Nat)) : Except String NativeOutcome).toOption.isNone

def base : Result :=
  { id := "native-outcome", suite := "repo", category := "test", status := "ok" }

-- Both the harness JSON (snake_case) and saved Result JSON (camelCase) keep string labels.
#guard wireCases.all fun (outcome, label) => Id.run do
  let result := base.withHarness <| Json.mkObj [("native_result", toJson label)]
  let saved := toJson result
  return result.nativeResult == some outcome &&
    (saved.getObjValAs? String "nativeResult").toOption == some label &&
    ((fromJson? saved : Except String Result).toOption.bind (·.nativeResult)) == some outcome &&
    result.csvRow[csvHeader.idxOf "native_result"]? == some label

#guard ((fromJson? (toJson base) : Except String Result).toOption.bind (·.nativeResult)).isNone

def exhausted (withCost : Bool) (head : String) : Result :=
  { base with
    command := some (if withCost then costCommand else plainCommand)
    nativeResult := some .exhausted
    propHead := some head }

#guard [false, true].all fun withCost =>
  ["State.Eval", "State.Return"].all fun head => (exhausted withCost head).fullyEvaluated
-- Current runs preserve the unfinished state, so an `Error` head is a disagreement.
#guard [false, true].all fun withCost => !(exhausted withCost "State.Error").fullyEvaluated
-- Runs recorded before the harness reported its command ended out of fuel in `Error`.
#guard ({ base with nativeResult := some .exhausted, propHead := some "State.Error" } : Result).fullyEvaluated
#guard !({ base with nativeResult := some .running, propHead := some "State.Eval" } : Result).fullyEvaluated

end Tests.Benchmark.NativeOutcome
