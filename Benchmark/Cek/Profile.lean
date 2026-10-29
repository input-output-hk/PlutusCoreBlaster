import Benchmark.Cek.Runner
import PlutusCore.UPLC.CekMachine.DecidableEq
import Lean.Data.Json
import Lean.Util.ShareCommon

/-! Diagnostic instrumentation, deliberately separate from the reference timing path.
Ordinary CEK transitions run in pure blocks between saturated builtin applications. We time
the existing `step` and `builtinCostSelected`, not copies of their implementations. Builtin
costs are still charged after execution, in the same reverse call order as `runStepsCosting`.
All durations are raw, inclusive of clock overhead; no estimated overhead is subtracted. -/

namespace Benchmark.Cek.Profile

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.ExBudget
open PlutusCore.UPLC.CostModels
open PlutusCore.UPLC.FlatEncoding.Internal
open Lean (Json toJson)

private def sem : PlutusCore.Default.BuiltinSemanticsVariant := .defaultFunSemanticsVariantE

structure BuiltinStats where
  builtin : BuiltinFun
  calls : Nat := 0
  evalNs : Nat := 0
  costNs : Nat := 0

private def addStats (stats : Array BuiltinStats) (b : BuiltinFun)
    (calls evalNs costNs : Nat) : Array BuiltinStats := Id.run do
  for h : i in [:stats.size] do
    if stats[i].builtin == b then
      let s := stats[i]
      return stats.set! i { s with
        calls := s.calls + calls
        evalNs := s.evalNs + evalNs, costNs := s.costNs + costNs }
  return stats.push ⟨b, calls, evalNs, costNs⟩

structure Segment where
  state : State
  fuel : Nat
  cost : ExBudget
  steps : Nat

/-- Stop before a builtin, at a terminal state, or at the fuel limit. This counts every
transition (including Return transitions), not only the ledger's charged Eval transitions. -/
private def advance (state : State) (fuel : Nat) (cost : ExBudget) (steps : Nat) : Segment :=
  match fuel, state with
  | _, .Halt _ | _, .Error | 0, _ => ⟨state, fuel, cost, steps⟩
  | n + 1, _ =>
    if (saturatedBuiltin? state).isSome then ⟨state, fuel, cost, steps⟩
    else advance (step sem state) n
      (cost + calculateStepCostr (semVarToCosts sem) state) (steps + 1)

@[noinline] private def runSegment (state : State) (fuel : Nat) (cost : ExBudget) : IO Segment :=
  pure (advance state fuel cost 0)

@[noinline] private def runBuiltin (state : State) : IO State := pure (step sem state)

@[noinline] private def runBuiltinCost (b : BuiltinFun) (args : List CekValue) : IO ExBudget :=
  pure (builtinCostSelected sem b args)

structure EvalStats where
  state : State
  cost : ExBudget
  machineSteps : Nat := 0
  machineNs : Nat := 0
  builtinEvalNs : Nat := 0
  builtinCostNs : Nat := 0
  costPassNs : Nat := 0
  totalNs : Nat := 0
  builtins : Array BuiltinStats := #[]

private def instrumentEval (program : Program) (maxSteps : Nat) : IO EvalStats := do
  let .Program _ body := program
  let start ← IO.monoNanosNow
  let mut state := initialState body
  let mut fuel := maxSteps
  let mut cost := ExBudget.zero
  let mut calls : List (BuiltinFun × List CekValue) := []
  let mut stats : EvalStats := { state, cost }
  repeat
    let startSegment ← IO.monoNanosNow
    let segment ← runSegment state fuel cost
    let elapsed := (← IO.monoNanosNow) - startSegment
    state := segment.state
    fuel := segment.fuel
    cost := segment.cost
    stats := { stats with
      machineNs := stats.machineNs + elapsed
      machineSteps := stats.machineSteps + segment.steps }
    match state with
    | .Halt _ | .Error => break
    | _ => pure ()
    if fuel == 0 then throw (IO.userError s!"CEK step limit exhausted ({maxSteps})")
    let some (b, args) := saturatedBuiltin? state
      | throw (IO.userError "profiler stopped outside a builtin")
    let startBuiltin ← IO.monoNanosNow
    let next ← runBuiltin state
    let elapsed := (← IO.monoNanosNow) - startBuiltin
    cost := cost + calculateStepCostr (semVarToCosts sem) state
    state := next
    fuel := fuel - 1
    calls := (b, args) :: calls
    stats := { stats with
      builtinEvalNs := stats.builtinEvalNs + elapsed
      builtins := addStats stats.builtins b 1 elapsed 0 }
  let startCost ← IO.monoNanosNow
  for (b, args) in calls do
    let startBuiltinCost ← IO.monoNanosNow
    let charge ← runBuiltinCost b args
    let elapsed := (← IO.monoNanosNow) - startBuiltinCost
    cost := cost + charge
    stats := { stats with
      builtinCostNs := stats.builtinCostNs + elapsed
      builtins := addStats stats.builtins b 0 0 elapsed }
  let costPassNs := (← IO.monoNanosNow) - startCost
  cost := (semVarToCosts sem).startupCost + cost
  let totalNs := (← IO.monoNanosNow) - start
  return { stats with state, cost, costPassNs, totalNs }

@[noinline] private def convertBytes (bytes : ByteArray) : IO String :=
  pure (String.mk (bytes.data.toList.map Char.ofUInt8))

@[noinline] private def expandBits (input : String) : IO (List Bool) :=
  match bitSequenceFromByteString input.data [] with
  | some bits => pure bits
  | none => throw (IO.userError "Flat bit expansion failed")

@[noinline] private def parseBits (bits : List Bool) : IO Program :=
  match decodeProgramFromBits bits with
  | some program => pure program
  | none => throw (IO.userError "Flat decode failed")

@[noinline] private def runDecode (bytes : ByteArray) : IO Program := IO.ofExcept (decode bytes)

@[noinline] private def referenceEval (program : Program) (fuel : Nat) : IO (State × ExBudget) :=
  pure (cekExecuteProgramWithCost sem program [] fuel)

private def timed (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoNanosNow
  let result ← action
  return (result, (← IO.monoNanosNow) - start)

structure DecodeStats where
  convertNs : Nat := 0
  bitsNs : Nat := 0
  parseNs : Nat := 0
  totalNs : Nat := 0

private def instrumentDecode (bytes : ByteArray) : IO (Program × DecodeStats) := do
  let start ← IO.monoNanosNow
  let (input, convertNs) ← timed (convertBytes bytes)
  let (bits, bitsNs) ← timed (expandBits input)
  let (program, parseNs) ← timed (parseBits bits)
  return (program, ⟨convertNs, bitsNs, parseNs, (← IO.monoNanosNow) - start⟩)

private def builtinJson (s : BuiltinStats) : Json := Json.mkObj [
  ("builtin", toJson (reprStr s.builtin)), ("calls", toJson s.calls),
  ("eval_ns", toJson s.evalNs), ("cost_ns", toJson s.costNs)]

/-- Closures can contain heavily shared environments: naive structural equality unfolds the
same DAG exponentially. Hash-cons the pair, then use Lean's sound pointer-equality shortcut.
This validation is outside every timer and does not modify either evaluated input. -/
private def sameState (a b : State) : Bool :=
  let (a, b) := Lean.ShareCommon.shareCommon (a, b)
  withPtrEq a b (fun _ => decide (a = b)) (by intro h; simp [h])

/-- Totals across RUNS, with uninstrumented baselines in the same process. Baseline and
instrumented order alternates to reduce systematic warm-cache/order bias. Validation,
file I/O, warm-up and JSON formatting are outside all reported timers. -/
def report (path : System.FilePath) (runs maxSteps : Nat) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let program ← runDecode bytes
  let expected ← referenceEval program maxSteps
  match expected.1 with
  | .Halt _ | .Error => pure ()
  | _ => throw (IO.userError s!"CEK step limit exhausted ({maxSteps})")
  let expectedOutcome : Outcome := ⟨(match expected.1 with | .Halt _ => true | _ => false), expected.2⟩
  -- Warm both paths, including the decoder and delayed costing pass.
  let _ ← instrumentDecode bytes
  let _ ← instrumentEval program maxSteps
  let mut clockSamples : Array Nat := #[]
  for _ in [:101] do
    let start ← IO.monoNanosNow
    clockSamples := clockSamples.push ((← IO.monoNanosNow) - start)
  let sortedClocks := clockSamples.qsort (· < ·)
  let clockPairNs := sortedClocks[50]!
  let clockPairP95Ns := sortedClocks[95]!
  let mut baseDecodeNs := 0
  let mut baseEvalNs := 0
  let mut ds : DecodeStats := {}
  let mut es : EvalStats := { state := expected.1, cost := expected.2 }
  for i in [:runs] do
    let baseline := do
      let (decoded, dns) ← timed (runDecode bytes)
      let (result, ens) ← timed (runEval program maxSteps)
      unless decoded == program && result == expectedOutcome do
        throw (IO.userError "reference outcome changed")
      pure (dns, ens)
    let instrumented := do
      let (decoded, d) ← instrumentDecode bytes
      let e ← instrumentEval program maxSteps
      unless decoded == program && sameState e.state expected.1 && e.cost == expected.2 do
        throw (IO.userError "profile differs from reference state or ExUnits")
      pure (d, e)
    let (dns, ens, d, e) ← if i % 2 == 0 then do
        let (dns, ens) ← baseline
        let (d, e) ← instrumented
        pure (dns, ens, d, e)
      else do
        let (d, e) ← instrumented
        let (dns, ens) ← baseline
        pure (dns, ens, d, e)
    baseDecodeNs := baseDecodeNs + dns
    baseEvalNs := baseEvalNs + ens
    ds := ⟨ds.convertNs + d.convertNs, ds.bitsNs + d.bitsNs,
      ds.parseNs + d.parseNs, ds.totalNs + d.totalNs⟩
    es := { es with
      machineSteps := es.machineSteps + e.machineSteps
      machineNs := es.machineNs + e.machineNs, builtinEvalNs := es.builtinEvalNs + e.builtinEvalNs,
      builtinCostNs := es.builtinCostNs + e.builtinCostNs,
      costPassNs := es.costPassNs + e.costPassNs, totalNs := es.totalNs + e.totalNs }
    for b in e.builtins do
      es := { es with builtins := addStats es.builtins b.builtin b.calls b.evalNs b.costNs }
  let builtinCalls := es.builtins.foldl (fun n s => n + s.calls) 0
  let result := Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("vm", toJson vm),
    ("script", toJson (scriptName path)), ("runs", toJson runs),
    ("status", toJson (match expected.1 with | .Halt _ => "ok" | _ => "error")),
    ("cpu", toJson expected.2.exBudgetCPU.unExCPU),
    ("mem", toJson expected.2.exBudgetMemory.unExMemory),
    ("clock_pair_median_ns", toJson clockPairNs),
    ("clock_pair_p95_ns", toJson clockPairP95Ns),
    ("baseline", Json.mkObj [("decode_ns", toJson baseDecodeNs), ("eval_ns", toJson baseEvalNs)]),
    ("decode", Json.mkObj [("bytes_to_string_ns", toJson ds.convertNs),
      ("string_to_bits_ns", toJson ds.bitsNs), ("flat_parse_ns", toJson ds.parseNs),
      ("total_ns", toJson ds.totalNs)]),
    ("eval", Json.mkObj [("machine_steps", toJson es.machineSteps),
      ("builtin_calls", toJson builtinCalls), ("machine_ns", toJson es.machineNs),
      ("builtin_eval_ns", toJson es.builtinEvalNs), ("builtin_cost_ns", toJson es.builtinCostNs),
      ("cost_pass_ns", toJson es.costPassNs), ("total_ns", toJson es.totalNs)]),
    ("builtins", toJson (es.builtins.qsort (fun a b => a.evalNs + a.costNs > b.evalNs + b.costNs)
      |>.map builtinJson))]
  IO.println result.pretty

end Benchmark.Cek.Profile
