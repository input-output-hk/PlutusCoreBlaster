import PlutusCore.UPLC.Term

namespace PlutusCore.Default

namespace Internal

open PlutusCore.UPLC.Term

/- Semantics variants depend on both the protocol version and the ledger language.

   Here's a table specifying the mapping in full (as of plutus 1.64.0.0 / Van Rossem era):

    plutus-version  pre-Conway  post-Conway
                 1           A            D
                 2           A            D
                 3           C            E

  I.e. for example

  - post-Conway 'PlutusV1' corresponds to 'DefaultFunSemanticsVariantD'
  - pre-Conway  'PlutusV2' corresponds to 'DefaultFunSemanticsVariantA'
  - post-Conway 'PlutusV3' corresponds to 'DefaultFunSemanticsVariantE'
  -/

/-- Plutus version. -/
inductive PlutusVersion
  | plutusV1
  | plutusV2
  | plutusV3

instance : Inhabited PlutusVersion where
  default := .plutusV3

/-- Models protocol versions. From UPLC semantics point-of-view,
    the only distinction is between pre-Conway and post-Conway
    eras. -/
inductive ProtocolVersion
  | preConway
  | postConway

instance : Inhabited ProtocolVersion where
  default := .postConway

/-- Builtin function semantic versions. Note that DefaultFunSemanticsVariantA,
    DefaultFunSemanticsVariantB etc. do not correspond directly to PlutusV1,
    PlutusV2 etc. in plutus-ledger-api. -/
inductive BuiltinSemanticsVariant
  | defaultFunSemanticsVariantA
  | defaultFunSemanticsVariantB
  | defaultFunSemanticsVariantC
  | defaultFunSemanticsVariantD
  | defaultFunSemanticsVariantE

instance : Inhabited BuiltinSemanticsVariant where
  default := .defaultFunSemanticsVariantE

def PlutusVersion.toSemanticsVariant : PlutusVersion → ProtocolVersion → BuiltinSemanticsVariant
  | .plutusV1, .preConway  => .defaultFunSemanticsVariantA
  | .plutusV1, .postConway => .defaultFunSemanticsVariantD
  | .plutusV2, .preConway  => .defaultFunSemanticsVariantA
  | .plutusV2, .postConway => .defaultFunSemanticsVariantD
  | .plutusV3, .preConway  => .defaultFunSemanticsVariantC
  | .plutusV3, .postConway => .defaultFunSemanticsVariantE

end Internal

export Internal
  (
    PlutusVersion
    ProtocolVersion
    BuiltinSemanticsVariant
    PlutusVersion.toSemanticsVariant
  )

end PlutusCore.Default
