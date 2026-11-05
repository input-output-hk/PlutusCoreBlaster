import Blaster.Smt.Model
import PlutusCore.Data

/-!
Decodes Blaster SMT model bindings into Plutus Data, lists, maps and byte strings.
Reuses Blaster's value parser and let expansion while interpreting Plutus constructors.
Rejects malformed values so callers can validate and replay concrete witnesses safely.
-/

namespace PlutusCore.Smt.Model

open PlutusCore.Data (Data)
open Blaster.Smt.Model (SExpr bindingValue integer constructor)

private partial def dataValue : SExpr → Option Data
  | .list [.atom ctor, n] =>
    if constructor ctor "I" then return .I (← integer n)
    else if constructor ctor "B" then
      match n with
      | .list [.atom maker, .text bytes] =>
        if constructor maker "mk" && bytes.data.all (fun c => c.toNat < 256)
        then some (.B ⟨bytes⟩) else none
      | _ => none
    else if constructor ctor "List" then return .List (← dataList n)
    else if constructor ctor "Map" then return .Map (← pairList n)
    else none
  | .list [.atom ctor, tag, fields] =>
    if constructor ctor "Constr" then return .Constr (← integer tag) (← dataList fields)
    else none
  | _ => none
where
  dataList : SExpr → Option (List Data)
    | .atom ctor => if ctor.startsWith "List.nil" then some [] else none
    | .list [.atom "as", value, _] => dataList value
    | .list [.atom ctor, head, tail] =>
      if ctor.startsWith "List.cons" then return (← dataValue head) :: (← dataList tail) else none
    | _ => none
  pairList : SExpr → Option (List (Data × Data))
    | .atom ctor => if ctor.startsWith "List.nil" then some [] else none
    | .list [.atom "as", value, _] => pairList value
    | .list [.atom ctor, .list [.atom pair, key, value], tail] =>
      if ctor.startsWith "List.cons" && pair.startsWith "Prod.mk" then
        return ((← dataValue key), (← dataValue value)) :: (← pairList tail)
      else none
    | _ => none

/-- Decode a named Plutus Data value from Blaster's model output. -/
def dataBinding (binding : String) : Option (String × Data) :=
  Blaster.Smt.Model.decodeBinding dataValue binding

/-- SMT queries can expose list/map/bytestring binders directly,
    rather than wrapped in a Data constructor. Reuse the same strict decoder. -/
private def wrappedBinding (wrapper : String) (binding : String) : Option (String × Data) := do
  let (name, value) ← bindingValue binding
  return (name, ← dataValue (.list [.atom wrapper, value]))

def listBinding (binding : String) : Option (String × List Data) := do
  let (name, .List items) ← wrappedBinding "Data.List" binding | none
  return (name, items)

def mapBinding (binding : String) : Option (String × List (Data × Data)) := do
  let (name, .Map items) ← wrappedBinding "Data.Map" binding | none
  return (name, items)

def byteStringBinding (binding : String) : Option (String × PlutusCore.ByteString.ByteString) := do
  let (name, .B bytes) ← wrappedBinding "Data.B" binding | none
  return (name, bytes)

end PlutusCore.Smt.Model
