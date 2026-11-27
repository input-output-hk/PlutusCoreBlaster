import PlutusCore.UPLC.Optimize.Extension.Recognize
import PlutusCore.UPLC.Optimize.Prefix

namespace PlutusCore.UPLC.Optimize
open Lean Meta
open Blaster.Optimize
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.Data (Data)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

open Recognize

@[blaster (register := false)]
theorem prefix_rule (sem : BuiltinSemanticsVariant) (block : Prefix sem) (fuel : Nat) :
    runSteps sem (Prefix.start sem block) fuel =
      if fuel < block.cost then .BudgetExhausted else
        runSteps sem block.target (fuel - block.cost) := Prefix.run_eq sem block fuel

private def liveState (s : Expr) : Bool :=
  s.isAppOfArity ``State.Eval 3 || s.isAppOfArity ``State.Return 2

/-- Restrict reduction to administrative transitions. In particular, stop
    before invoking saturated builtins and before entering force/case loop
    bodies, so the pass neither computes cryptography nor unrolls a list. -/
private def administrativeState (s : Expr) : Bool := Id.run do
  if let some fields := args? s ``State.Eval 3 then
    let code := fields[2]!.consumeMData
    if code.isConstOf ``PlutusCore.UPLC.Term.Term.Error then return false
    if let some force := args? code ``Term.Force 1 then
      if force[0]!.isAppOfArity ``Term.Case 2 then return false
    return true
  if let some fields := args? s ``State.Return 2 then
    let some cell := args? fields[0]! ``List.cons 3 | return false
    let frame := cell[1]!
    let mut callee := fields[1]!
    if let some right := args? frame ``Frame.RightApplicationOfValue 1 then
      callee := right[0]!
    else if frame.isAppOfArity ``Frame.LeftApplicationToValue 1 || frame.isConstOf ``Frame.ForceFrame then
      pure ()
    else return true
    if let some builtin := args? callee ``CekValue.VBuiltin 3 then
      return builtin[2]!.isAppOfArity ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.More 2
    return callee.isAppOfArity ``CekValue.VLam 2 || callee.isAppOfArity ``CekValue.VDelay 2
  return false

private def administrativeStep? (sem state : Expr) : TranslateEnvT (Option Expr) := do
  unless administrativeState state do return none
  try
    let target := (← whnf (mkApp2 (mkConst ``step) sem state)).consumeMData
    if liveState target then return some target else return none
  catch _ => return none

initialize registerTraceClass `Optimize.cekPrefix

/-- Fuse a bounded deterministic block and carry its definitional certificate.
    Payloads and unused environments are never recursively normalized here.
    This also works with symbolic remaining fuel introduced by a loop summary. -/
@[blaster runSteps]
def optimizeAdministrativePrefix (f : Expr) (args : Array Expr) : TranslateEnvT (Option Expr) := do
  if args.size != 3 then return none
  let state := args[1]!.consumeMData
  if state.hasMVar || state.hasLevelMVar || !liveState state then return none
  let mut target := state
  let mut cost := 0
  let mut stopped := false
  let mut seen : Std.HashSet Expr := {}
  for _ in [:32] do
    if seen.contains target then return none
    seen := seen.insert target
    let some next ← administrativeStep? args[0]! target |
      stopped := true
      break
    target := next
    cost := cost + 1
  if !stopped || cost < 2 || target.hasMVar || target.hasLevelMVar then return none
  let proof ← mkEqRefl target
  let block := mkAppN (mkConst ``Prefix.mk)
    #[args[0]!, state, target, mkNatLit cost, proof, mkConst ``True.intro]
  let canonical := mkApp2 (mkConst ``Prefix.start) args[0]! block
  trace[Optimize.cekPrefix] "fused {cost} administrative transitions"
  blaster_opt_prefix_rule f #[args[0]!, canonical, args[2]!]

end PlutusCore.UPLC.Optimize
