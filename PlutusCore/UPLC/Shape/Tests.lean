import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.ScriptEncoding
import PlutusCore.UPLC.Shape.Basic

namespace PlutusCore.UPLC.Shape

open PlutusCore.UPLC.ScriptEncoding
open PlutusCore.UPLC.Shape.Internal
open PlutusCore.UPLC.Term

/-! ### Rendering of the lattice -/

example : toString (.ConInteger : TermShape)                                               = "Int"                            := by decide +native
example : toString (.Function .ConInteger (.Function .ConInteger .ConInteger) : TermShape) = "Int → Int → Int"              := by decide +native
example : toString (.Alternatives [.ConInteger, .ConString, .ConByteString] : TermShape)   = "Int | String | ByteString"      := by decide +native
example : toString (.ListSh [.ConInteger, .ConByteString] .Anything : TermShape)           = "[Int, ByteString, …]"          := by decide +native
example : toString (.PairSh .ConInteger .ConString : TermShape)                            = "(Int, String)"                  := by decide +native
example : toString (.DataSh (.DConstr (some 0) [.DInt, .DBytes] .DNone) : TermShape)       = "Data.Constr 0 (Data.I, Data.B)" := by decide +native
example : toString (.Constr none [.ConInteger] : TermShape)                                = "Constr ? (Int)"                 := by decide +native

/-! ### `analyzeType`: scalars, builtins, functions -/

example : toString (analyzeType (.Const (.Integer 42)))                                  = "Int"                         := by decide +native
example : toString (analyzeType (.Lam "x" (.Const (.Bool true))))                        = "Anything → Bool"            := by decide +native
example : toString (analyzeType (.Builtin .AddInteger))                                  = "Int → Int → Int"           := by decide +native
example : toString (analyzeType (.Apply (.Builtin .AddInteger) (.Const (.Integer 42))))  = "Int → Int"                  := by decide +native
-- provable crash: a String constant where Int is demanded
example : toString (analyzeType (.Apply (.Builtin .AddInteger) (.Const (.String "42")))) = "Nothing"                     := by decide +native
example : toString (analyzeType (.Builtin .IfThenElse))                                  = "Delay (Bool → α → α → α)" := by decide +native
example : toString (analyzeType (.Force (.Builtin .IfThenElse)))                         = "Bool → α → α → α"         := by decide +native
-- provable crash: a Unit constant where Bool is demanded
example : toString (analyzeType (.Apply (.Force (.Builtin .IfThenElse)) (.Const .Unit))) = "Nothing"                     := by decide +native
example : toString (analyzeType (.Apply (.Force (.Builtin .IfThenElse)) (.Const (.Bool true)))) = "α → α → α"          := by decide +native
example : toString (analyzeType (.Builtin .EqualsInteger))                               = "Int → Int → Bool"          := by decide +native
example : toString (analyzeType (.Force (.Builtin .HeadList)))                           = "[…α] → α"                  := by decide +native
example : toString (analyzeType .Error)                                                  = "Nothing"                     := by decide +native

/-! ### Higher-order linkage (type variables) -/

example : toString (analyzeType (.Lam "x" (.Apply (.Var "x") (.Const (.Integer 42)))))      = "(Int → α) → α"                  := by decide +native
example : toString (analyzeType (.Lam "f" (.Lam "x" (.Apply (.Var "f") (.Var "x")))))       = "(Anything → α) → Anything → α" := by decide +native
example : toString (analyzeType (.Force (.Force (.Builtin .ChooseList))))                   = "[…α] → β → β → β"             := by decide +native

/-! ### `Case` / `Constr` -/

-- literal Constr, nullary fields: branch selected and applied to no fields
example : toString (analyzeType (.Case (.Constr 0 []) [.Const (.Integer 1), .Const (.Integer 2)]))         = "Int"                      := by decide +native
-- literal Constr with a field but a nullary branch ⇒ arity mismatch ⇒ provable crash
example : toString (analyzeType (.Case (.Constr 0 [.Const (.Integer 1)]) [.Const (.Integer 1)]))           = "Nothing"                  := by decide +native
example : toString (analyzeType (.Constr 0 [.Const (.Integer 1)]))                                         = "Constr 0 (Int)"           := by decide +native
-- non-Constr scrutinee ⇒ union of branch results
example : toString (analyzeType (.Case (.Const (.Bool true)) [.Const (.Integer 1), .Const (.String "a")])) = "Int | String"             := by decide +native
-- unknown-tag Case on a variable: reconstructs the sum-of-products type from the branch
-- eliminators (scrutinee demanded `Constr ?`, branch results joined into the union)
example : toString (analyzeType (.Lam "x" (.Case (.Var "x") [.Const (.Integer 1), .Const (.String "a")]))) = "Constr 0 | Constr 1 → Int | String" := by decide +native

/-! ### Heterogeneous `ifThenElse` branches ⇒ union -/

example : toString (analyzeType
    (.Force
      (.Apply
        (.Apply
          (.Apply (.Force (.Builtin .IfThenElse)) (.Const (.Bool true)))
          (.Delay (.Const (.Integer 1))))
        (.Delay (.Const (.String "x"))))))
        = "Int | String" := by decide +native

/-! ### Structural discovery -/

-- λdatum. unIData (headList (sndPair (unConstrData datum)))
-- discovers: datum is a Data.Constr whose field 0 is Data.I (open tail: length unchecked).
example : toString (analyzeType
    (.Lam "datum"
      (.Apply (.Builtin .UnIData)
        (.Apply (.Force (.Builtin .HeadList))
          (.Apply (.Force (.Force (.Builtin .SndPair)))
            (.Apply (.Builtin .UnConstrData) (.Var "datum")))))))
        = "Data.Constr ? (Data.I, …) → Int" := by decide +native

-- positional: two distinct fields of the same datum discovered separately (no clash), using
-- a shared `fields` binding as compiled code does
example : toString (analyzeType
  (.Lam "d" (.Apply
    (.Lam "fields" (.Apply (.Apply (.Builtin .AddInteger)
        (.Apply (.Builtin .UnIData) (.Apply (.Force (.Builtin .HeadList)) (.Var "fields"))))
        (.Apply (.Builtin .UnIData) (.Apply (.Force (.Builtin .HeadList)) (.Apply (.Force (.Builtin .TailList)) (.Var "fields"))))))
    (.Apply (.Force (.Force (.Builtin .SndPair))) (.Apply (.Builtin .UnConstrData) (.Var "d"))))))
        = "Data.Constr ? (Data.I, Data.I, …) → Int" := by decide +native

-- nested: field 0 of the datum is itself a Data.Constr
example : toString (analyzeType
  (.Lam "d" (.Apply (.Builtin .UnConstrData) (.Apply (.Force (.Builtin .HeadList))
    (.Apply (.Force (.Force (.Builtin .SndPair))) (.Apply (.Builtin .UnConstrData) (.Var "d")))))))
        = "Data.Constr ? (Data.Constr ?, …) → (Int, […Data])" := by decide +native

-- chooseData with only the `I` branch live ⇒ argument narrows to Data.I
example : toString (analyzeType
  (.Lam "d"
    (.Force
      (.Apply
        (.Apply
          (.Apply
            (.Apply
              (.Apply
                (.Apply (.Force (.Builtin .ChooseData)) (.Var "d"))
                (.Delay .Error))
              (.Delay .Error))
            (.Delay .Error))
          (.Delay (.Const (.Integer 1))))
        (.Delay .Error)))))
        = "Data.I → Int" := by decide +native

-- positional head/tail navigate a list's positions (not meet-all-positions)
example : toString (analyzeType (.Apply (.Force (.Builtin .HeadList))
  (.Const (.ConstList [.Integer 1, .Bool true])))) = "Int" := by decide +native
example : toString (analyzeType (.Apply (.Force (.Builtin .HeadList))
  (.Apply (.Force (.Builtin .TailList))
    (.Const (.ConstList [.Integer 1, .Bool true]))))) = "Bool" := by decide +native

-- pair projection
example : toString (analyzeType (.Lam "p" (.Apply (.Force (.Force (.Builtin .FstPair))) (.Var "p"))))
        = "(α, β) → α" := by decide +native

/-! ### Recursion / self-application (bounded fixpoint) does not collapse to `Nothing`. -/

-- contravariant self-reference widens to `Anything` (no μ needed)
example : toString (analyzeType (.Lam "x" (.Apply (.Var "x") (.Var "x"))))
        = "(Anything → α) → α" := by decide +native
-- a value consed onto a list of itself forms an equirecursive (μ) type
example : toString (analyzeType
    (.Lam "x" (.Apply (.Apply (.Force (.Builtin .MkCons)) (.Var "x")) (.Var "x"))))
        = "[…μρ. […ρ]] → […μρ. […ρ]]" := by decide +native

-- `if tag==0 then … else error` reconstructs the Data.Constr tag
example :
  (let tag : Term.Term :=
     .Apply (.Force (.Force (.Builtin .FstPair)))
            (.Apply (.Builtin .UnConstrData) (.Var "d"))
   let cond : Term.Term :=
     .Apply (.Apply (.Builtin .EqualsInteger) tag) (.Const (.Integer 0))
   let ite : Term.Term :=
     .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) cond)
                    (.Delay (.Const (.Integer 1))))
            (.Delay .Error)
   toString (analyzeType (.Lam "d" (.Force ite)))) = "Data.Constr 0 → Int" := by decide +native

-- A let-bound function is unrolled/inlined at its call site (context-sensitively),
-- so `(λid. id 1) (λx. x)` recovers `Int` rather than the summary's `Anything`
example : toString (analyzeType
  (.Apply (.Lam "id" (.Apply (.Var "id") (.Const (.Integer 1))))
    (.Lam "x" (.Var "x")))) = "Int" := by decide +native

-- capture-avoiding reduction: `(λx. λw. x) (addInteger w 1)` must α-rename the inner `w`,
-- so the free `w` in the argument is NOT captured. Correct: `Anything → Int` (the returned
-- constant function ignores its own argument); a naive substitution would give `Int → Int`.
example : toString (analyzeType
  (.Apply (.Lam "x" (.Lam "w" (.Var "x")))
    (.Apply (.Apply (.Builtin .AddInteger) (.Var "w"))
      (.Const (.Integer 1))))) = "Anything → Int" := by decide +native

/-! ### The auction script (end-to-end): resolves to a readable signature, not `Nothing`. -/

/-- info: Successfully decoded single CBOR hex 'PlutusCore/UPLC/Shape/auction.cbor_hex' -/
#guard_msgs in
#import_uplc auction PlutusV3 single_cbor_hex "PlutusCore/UPLC/Shape/auction.cbor_hex"

def programBody : Term.Program → Term.Term
  | .Program _ body => body

-- A PlutusV3 validator takes a single argument — the ScriptContext (a Data.Constr). Its
-- fields are consumed by a recursive fold the analyzer widens through, so no per-field
-- structure is recovered here (fold-traversed values fall back to `Data.Constr ?`); direct
-- destructuring, by contrast, is discovered positionally (see the tests above).
example : toString (analyzeType (programBody auction.script))
        = "Data.Constr ? → Unit" := by decide +native

end PlutusCore.UPLC.Shape
