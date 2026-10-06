import PlutusCore.Data
import PlutusCore.Integer
import PlutusCore.ByteString

namespace PlutusCore.IsData

open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open PlutusCore.ByteString (ByteString)

/-- Typeclass for Lean types that can be encoded to and decoded from Plutus `Data`.
    Mirrors `PlutusTx.IsData` / `cardano-api`'s `FromData`/`ToData`. -/
class IsData (α : Type u) where
  toData   : α → Data
  fromData : Data → Option α

instance : IsData Data where
  toData   := id
  fromData := some

instance : IsData Integer where
  toData   := Data.I
  fromData | Data.I x => some x | _ => none

instance : IsData ByteString where
  toData   := Data.B
  fromData | Data.B b => some b | _ => none

instance : IsData Bool where
  toData b := if b then Data.Constr 1 [] else Data.Constr 0 []
  fromData
  | Data.Constr 0 [] => some false
  | Data.Constr 1 [] => some true
  | _                => none

instance : IsData Unit where
  toData   _ := Data.Constr 0 []
  fromData | Data.Constr 0 [] => some () | _ => none

/-- On-chain `Data` has no text type; a schema `#string` field is carried as a
    `ByteString` payload (mirroring how `ByteString` already wraps a `String`). -/
instance : IsData String where
  toData   s := Data.B { data := s }
  fromData | Data.B b => some b.data | _ => none

instance [IsData α] : IsData (Option α) where
  toData | none   => Data.Constr 1 []
         | some x => Data.Constr 0 [IsData.toData x]
  fromData | Data.Constr 1 []  => some none
           | Data.Constr 0 [x] => (IsData.fromData x).map some
           | _                 => none

instance [IsData α] : IsData (List α) where
  toData xs := Data.List (xs.map IsData.toData)
  fromData | Data.List xs => xs.mapM IsData.fromData | _ => none

instance [IsData α] [IsData β] : IsData (α × β) where
  toData p := Data.Constr 0 [IsData.toData p.1, IsData.toData p.2]
  fromData | Data.Constr 0 [a, b] => do
                let a' ← IsData.fromData a
                let b' ← IsData.fromData b
                return (a', b')
           | _ => none

end PlutusCore.IsData
