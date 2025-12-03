import Lean.Expr
import Lean.ToLevel

open Lean

def listToExprLoop {α} (aToExpr : α → Expr) (consFn : Expr) (acc : Expr) : List α → Expr
  | []      => acc
  | a :: as => listToExprLoop aToExpr consFn (mkApp2 consFn (aToExpr a) (acc)) as

def listToExpr {α : Type u} [ToLevel.{u}] (aType : Expr) (aToExpr : α → Expr) (as : List α) : Expr :=
  let nil  := .app (.const ``List.nil  [toLevel.{u}]) aType
  let cons := .app (.const ``List.cons [toLevel.{u}]) aType
  listToExprLoop aToExpr cons nil (List.reverse as)

def pairToExpr {α : Type u} [ToLevel.{u}] (aToExpr : α → Expr) (p : α × α) : Expr :=
  mkApp2 (.const ``Prod.mk []) (aToExpr p.1) (aToExpr p.2)
