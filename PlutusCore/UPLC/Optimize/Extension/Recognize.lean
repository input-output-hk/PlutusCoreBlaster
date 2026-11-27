import Blaster.Optimize.Basic
import PlutusCore.UPLC.Optimize.ScalarSearch

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

namespace Recognize

def args? (e : Expr) (name : Name) (arity : Nat) : Option (Array Expr) :=
  if e.isAppOfArity name arity then some e.getAppArgs else none

def listItem? (e : Expr) (index : Nat) : Option Expr := do
  let cell ← args? e ``List.cons 3
  match index with
  | 0 => some cell[1]!
  | n + 1 => listItem? cell[2]! n

def capIndexFrom? (binderCount : Nat) (e : Expr) : Option Nat := do
  let v ← args? e ``Term.Var 1
  let .lit (.natVal n) := v[0]! | none
  if n < binderCount then none else some (n - binderCount)

def capIndex? (e : Expr) : Option Nat := capIndexFrom? 2 e
def closedDefEq (a b : Expr) : TranslateEnvT Bool := do
  if a.hasFVar || b.hasFVar || a.hasMVar || b.hasMVar || a.hasLevelMVar || b.hasLevelMVar then
    return false
  isDefEq a b
def valueArgs (n : Nat) : Expr :=
  if n ≤ 1 then mkApp (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.One)
    (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV)
  else mkApp2 (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArgs.More)
    (mkConst ``PlutusCore.UPLC.Builtins.ExpectedBuiltinArg.ArgV) (valueArgs (n - 1))
termination_by n

def builtinValue (b : Name) (n : Nat) : Expr :=
  mkApp3 (mkConst ``CekValue.VBuiltin) (mkConst b)
    (mkApp (mkConst ``List.nil [.zero]) (mkConst ``CekValue)) (valueArgs n)

def certifyBindings (env layout : Expr) (indices : Array Nat) :
    TranslateEnvT (Option Expr) := do
  let mut proofs : Array Expr := #[]
  for (i, b, n) in #[(indices[0]!, ``BuiltinFun.IfThenElse, 3),
      (indices[1]!, ``BuiltinFun.ChooseList, 3),
      (indices[2]!, ``BuiltinFun.HeadList, 1), (indices[3]!, ``BuiltinFun.TailList, 1)] do
    let some actual := listItem? env i | return none
    let expected := builtinValue b n
    unless ← closedDefEq actual expected do return none
    let someValue := mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``CekValue) expected
    proofs := proofs.push (← mkEqRefl someValue)
  return some (mkAppN (mkConst ``ScalarSearch.Bindings.mk) (#[env, layout] ++ proofs))

end Recognize

end PlutusCore.UPLC.Optimize
