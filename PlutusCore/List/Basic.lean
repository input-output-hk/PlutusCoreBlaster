
namespace PlutusCore.List

/-! ## Formalisation for PlutusCore List representation and builtin functions. -/

namespace PlutusCore.ListInternal

-- We here use the Lean4 List representation

/-! ## Builtin List functions. -/

/-- Given List `xs` and arguments `t1` and t2`, perform the following:
      - when `xs = []` return `t1`
      - when `xs = [x₁, ..., xₙ]` return `t2`

    NOTE: `PLC.chooseList` is defined as a macro rule mainly for Lean
    to be able to detect that functions recursively defined as follows
    satisfy strutural recursion.
      `go (l : List β) : List α :=
          PLC.chooseList l (fun _ => []) (fun _ => f (head l) :: go (tail l))`

    Signature: `chooseList : List α → β → β → β`
-/
macro_rules
| `(UPLC.chooseList $xs $t1 $t2) =>
      `(if List.isEmpty $xs then $t1 else $t2)

/-- Given a default value `n`, function `f` and List `xs`,
    `caseList n f xs` is defined as follows:
      := n        if xs = []
      := f h tl   if xs = h :: tl
    NOTE: `PLC.caseList` is defined as a macro rule mainly for Lean
    to be able to detect that functions recursively defined as follows
    satisfy strutural recursion.
      `go (l : List β) : List α :=
          PLC.caseList [] (fun x xs => f x :: go xs) l`

    Signature: `PLC.caseList : β → (α → List α → β) → List α → β`
-/
macro_rules
| `(UPLC.caseList $n $f $xs) =>
       `(if let h :: tl := $xs then $f h tl else $n)


/-- Given element `x` and List `[x₁, ..., xₙ]` return `[x, x₁, ..., xₙ]` -/
def mkCons (x : α) (xs : List α) : List α := x :: xs

/-- Given List `xs` returns the head of the list
    An error is triggered when `xs` is empty.
-/
def headList (xs : List α) : Except String α :=
  match xs with
  | [] => throw "headList: empty list"
  | x :: _ => pure x

/-- Given List `xs` returns the tail of the list
    An error is triggered when `xs` is empty.
-/
def tailList (xs : List α) : Except String (List α) :=
  match xs with
  | [] => throw "tailList: empty list"
  | _ :: tl => pure tl

/-- Given List `xs`, return `true` only when `xs` is empty.
    Otherwise `false`
-/
def nullList (xs : List α) : Bool := xs.isEmpty

end PlutusCore.ListInternal

export PlutusCore.ListInternal
  ( -- NOTE: macro rules chooseList, caseList are implicitly exported
    headList
    mkCons
    nullList
    tailList
  )

end PlutusCore.List

