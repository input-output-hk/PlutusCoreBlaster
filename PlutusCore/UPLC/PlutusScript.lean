import PlutusCore.UPLC.Term

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
