import PlutusCore.UPLC.Term
import PlutusCore.Default

namespace PlutusCore.UPLC.PlutusScript
open Term (Program)

/-- The Plutus ledger language
    NOTE: This is different from `UPLC.Version`
-/
inductive PlutusLanguage
  | PlutusV1 : PlutusLanguage
  | PlutusV2 : PlutusLanguage
  | PlutusV3 : PlutusLanguage
deriving Repr

/-- The `PlutusVersion` the cost model and builtin semantics are selected by. -/
def PlutusLanguage.toPlutusVersion : PlutusLanguage → PlutusCore.Default.PlutusVersion
  | .PlutusV1 => .plutusV1
  | .PlutusV2 => .plutusV2
  | .PlutusV3 => .plutusV3

/-- Plutus script envelope type
    NOTE: This structure can be extended to also include the script hash which can correspond
    to the applied/unapplied script hash.
-/
structure PlutusScript where
  /-- Plutus ledger language considered for the import UPLC program -/
  lang : PlutusLanguage
  /-- uplc program -/
  script : Program
deriving Repr


end PlutusCore.UPLC.PlutusScript
