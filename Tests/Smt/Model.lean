import PlutusCore.Smt.Model

namespace Tests.Smt.Model

open Lean (Json)

def decoded (s : String) : Option Json :=
  (PlutusCore.Smt.Model.dataBinding s).map (fun (_, value) => PlutusCore.Data.toDetailedJson value)

#guard decoded "datum: (Data.I (- 42))" == (Json.parse "{\"int\":-42}").toOption

-- Colons inside strings must not split bindings. Quotes and Unicode escapes use
-- SMT-LIB conventions; the output is lossless Plutus detailed-schema JSON.
#guard decoded "datum: (Data.B (ByteString.mk \"a: \"\"q\"\"\\u{0}\\u{ff}\"))" ==
  (Json.parse "{\"bytes\":\"613a2022712200ff\"}").toOption

#guard decoded "datum: (Data.Constr 0 (List.cons (Data.I 3) List.nil))" ==
  (Json.parse "{\"constructor\":0,\"fields\":[{\"int\":3}]}").toOption

#guard decoded "datum: (Data.Map (List.cons (Prod.mk (Data.I 1) (Data.List (List.cons (Data.B (ByteString.mk \"x\")) List.nil))) List.nil))" ==
  (Json.parse "{\"map\":[{\"k\":{\"int\":1},\"v\":{\"list\":[{\"bytes\":\"78\"}]}}]}").toOption

#guard (decoded "datum: (Data.I 3) trailing").isNone
#guard (decoded "datum: (Data.I not_an_integer)").isNone
#guard (decoded "datum: (Data.B (ByteString.mk \"\\u{100}\"))").isNone

-- Real constructor-valued countermodels contain shared, nested let expressions.
#guard decoded "datum: (let ((x (Data.I 7))) (Data.Constr 0 (List.cons x List.nil)))" ==
  decoded "datum: (Data.Constr 0 (List.cons (Data.I 7) List.nil))"
#guard decoded "datum: (let ((x (Data.I 7))) (let ((x (Data.I 8)) (y x)) (Data.List (List.cons x (List.cons y List.nil)))))" ==
  decoded "datum: (Data.List (List.cons (Data.I 8) (List.cons (Data.I 7) List.nil)))"

-- Typed spending parameters appear without their enclosing Data constructors.
#guard (Blaster.Smt.Model.integerBinding "fee: (- 98765432101234567890)") ==
  some ("fee", -98765432101234567890)
#guard ((PlutusCore.Smt.Model.listBinding
    "referenceInputs: (List.cons_Data (Data.I 42) List.nil_Data)").map
    (fun (_, xs) => PlutusCore.Data.toDetailedJson (.List xs))) ==
  (Json.parse "{\"list\":[{\"int\":42}]}").toOption
#guard ((PlutusCore.Smt.Model.mapBinding
    "mint: (List.cons_Prod (Prod.mk_Data (Data.I 1) (Data.I 2)) List.nil_Prod)").map
    (fun (_, xs) => PlutusCore.Data.toDetailedJson (.Map xs))) ==
  (Json.parse "{\"map\":[{\"k\":{\"int\":1},\"v\":{\"int\":2}}]}").toOption
#guard ((PlutusCore.Smt.Model.byteStringBinding "txId: (ByteString.mk \"a: \\u{ff}\")").map
    (fun (_, bytes) => PlutusCore.Data.toDetailedJson (.B bytes))) ==
  (Json.parse "{\"bytes\":\"613a20ff\"}").toOption
#guard (PlutusCore.Smt.Model.listBinding "inputs: List.nil_Data trailing").isNone
#guard (PlutusCore.Smt.Model.mapBinding "mint: (List.cons (Data.I 1) List.nil)").isNone

-- Z3 qualifies polymorphic empty lists with their sort in real model values.
#guard ((PlutusCore.Smt.Model.listBinding
    "referenceInputs: (List.cons (PlutusCore.Data.PlutusCore.DataInternal.Data.I 42) (as List.nil (@List @PlutusCore.Data.PlutusCore.DataInternal.Data)))").map
    (fun (_, xs) => PlutusCore.Data.toDetailedJson (.List xs))) ==
  (Json.parse "{\"list\":[{\"int\":42}]}").toOption
#guard ((PlutusCore.Smt.Model.mapBinding
    "mint: (List.cons (Prod.mk (Data.I 1) (Data.I 2)) (as List.nil MapEntryList))").map
    (fun (_, xs) => PlutusCore.Data.toDetailedJson (.Map xs))) ==
  (Json.parse "{\"map\":[{\"k\":{\"int\":1},\"v\":{\"int\":2}}]}").toOption

end Tests.Smt.Model
