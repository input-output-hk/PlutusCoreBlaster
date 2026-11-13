import PlutusCore.UPLC.Term

namespace PlutusCore.Default

namespace Internal

open PlutusCore.UPLC.Term

/- Semantics variants depend on both the protocol version and the ledger language.

   Here's the mapping in plutus 1.64.0.0 (`MachineParameters.hs` and the
   per-language `EvaluationContext.hs`), by major protocol version:

    plutus-version  PV 5–8 (preConway)  PV 9–10 (postConwayPreVanRossem)  PV ≥ 11 (postVanRossem)
                 1                   A                                 B                        D
                 2                   A                                 B                        D
                 3                   —                                 C                        E

  PlutusV3 is only available from protocol version 9.

  `PlutusVersion.toSemanticsVariant` doesn't follow the middle column yet: it
  returns D for V1/V2 and E for V3 there (#86).
  -/

/-- Plutus version. -/
inductive PlutusVersion
  | plutusV1
  | plutusV2
  | plutusV3

instance : Inhabited PlutusVersion where
  default := .plutusV3

/-- Models protocol versions. The ledger picks the builtin semantics variant,
    and whether `case` may dispatch on a non-`constr` scrutinee (an
    `Integer`/`Bool`/`List`/`Pair` value, as opposed to a `constr` value), from
    the major protocol version. Three ranges matter:
    - `preConway`: protocol versions 5–8;
    - `postConwayPreVanRossem`: 9–10 (Chang and Plomin);
    - `postVanRossem`: 11 onward. The van Rossem hard fork switches V1/V2 to
      variant D and V3 to variant E, and enables `case` on constants. -/
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

/-- The builtin semantics variant the ledger uses for a language at a protocol
    version. Known gap (#86): Plutus 1.64 uses B for V1/V2 and C for V3 at
    `postConwayPreVanRossem`, but this still returns D and E there. -/
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
