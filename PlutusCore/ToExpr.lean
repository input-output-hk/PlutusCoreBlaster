import Lean

open Lean

def integerToExpr (n : Int) : Expr :=
  match n with
  | Int.ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | Int.negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

def listToExprLoop {α} (aToExpr : α → Expr) (consFn : Expr) (acc : Expr) : List α → Expr
  | []      => acc
  | a :: as => listToExprLoop aToExpr consFn (mkApp2 consFn (aToExpr a) (acc)) as

def listToExpr {α : Type u} [ToLevel.{u}] (aType : Expr) (aToExpr : α → Expr) (as : List α) : Expr :=
  let nil  := .app (.const ``List.nil  [toLevel.{u}]) aType
  let cons := .app (.const ``List.cons [toLevel.{u}]) aType
  listToExprLoop aToExpr cons nil (List.reverse as)

def arrayToExpr {α : Type u} [ToLevel.{u}] (aType : Expr) (aToExpr : α → Expr) (as : Array α) : Expr :=
  mkApp2 (mkConst ``List.toArray [toLevel.{u}]) aType (listToExpr aType aToExpr as.toList)

def pairToExpr {α : Type u} [ToLevel.{u}] {β : Type v} [ToLevel.{v}] (aType: Expr) (bType : Expr) (aToExpr : α → Expr) (bToExpr : β → Expr) (p : α × β) : Expr :=
  mkApp4 (.const ``Prod.mk [toLevel.{u}, toLevel.{v}]) aType bType (aToExpr p.1) (bToExpr p.2)
