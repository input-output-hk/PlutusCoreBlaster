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

/-- Models protocol versions. From the builtin-semantics-variant point of
    view, the only distinction is between pre-Conway and post-Conway eras;
    but `case` on a non-`constr` scrutinee (an `Integer`/`Bool`/`List`/`Pair`
    value, as opposed to a `constr` value) is a separate, later capability
    that only became available at the Van Rossem hard fork (protocol version
    11), strictly inside what is otherwise "post-Conway" (protocol version 9
    onward). Hence three states rather than two. -/
inductive ProtocolVersion
  | preConway
  | postConwayPreVanRossem
  | postVanRossem

/-- Defaults to the current real chain state. The Van Rossem hard fork
    (protocol version 11) went live on mainnet 2026-07-18, so `postVanRossem`
    -- not `postConwayPreVanRossem` (Plomin, protocol version 10) -- is
    correct as of this writing. Update this default (and re-check every
    other hardcoded assumption of "current" protocol version in this repo)
    when the next hard fork ships. -/
instance : Inhabited ProtocolVersion where
  default := .postVanRossem

/-- Whether `case` may dispatch on a non-`constr` scrutinee (an `Integer`,
    `Bool`, `List`, `Pair`, etc. value) rather than only a `constr` value.
    Live from the Van Rossem hard fork onward. -/
def ProtocolVersion.supportsCaseOnConstants : ProtocolVersion → Bool
  | .preConway              => false
  | .postConwayPreVanRossem => false
  | .postVanRossem          => true

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
  | .plutusV1, .preConway              => .defaultFunSemanticsVariantA
  | .plutusV1, .postConwayPreVanRossem => .defaultFunSemanticsVariantD
  | .plutusV1, .postVanRossem          => .defaultFunSemanticsVariantD
  | .plutusV2, .preConway              => .defaultFunSemanticsVariantA
  | .plutusV2, .postConwayPreVanRossem => .defaultFunSemanticsVariantD
  | .plutusV2, .postVanRossem          => .defaultFunSemanticsVariantD
  | .plutusV3, .preConway              => .defaultFunSemanticsVariantC
  | .plutusV3, .postConwayPreVanRossem => .defaultFunSemanticsVariantE
  | .plutusV3, .postVanRossem          => .defaultFunSemanticsVariantE

end Internal

export Internal
  (
    PlutusVersion
    ProtocolVersion
    BuiltinSemanticsVariant
    PlutusVersion.toSemanticsVariant
  )

end PlutusCore.Default
