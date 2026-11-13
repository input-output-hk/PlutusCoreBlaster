import Blaster
import PlutusCore.Default
import PlutusCore.UPLC.BuiltinFunctions.Data

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/33
--
-- In Plutus 1.64, semantics variants D (V1/V2) and E (V3), used from protocol
-- version 11, read `ConstrData`'s constructor index as a Word64, so an index
-- outside [0, 2^64 - 1] fails the builtin. Variants A–C, used before protocol
-- version 11, accept any Integer.
namespace Tests.Issue33

open PlutusCore.Default (BuiltinSemanticsVariant)
open PlutusCore.UPLC.BuiltinFunctions.Data
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term (Const)

set_option warn.sorry false

-- 2^64 - 1, Word64's maximum representable value.
private def word64Max : PlutusCore.Integer.Integer := 18446744073709551615

private def constrDataAt (sv : BuiltinSemanticsVariant) (i : PlutusCore.Integer.Integer) :
    Option CekValue :=
  constrData sv [CekValue.VCon (Const.ConstDataList []), CekValue.VCon (Const.Integer i)]

-- Under D the index range is exactly [0, 2^64 - 1].
example : constrDataAt .defaultFunSemanticsVariantD 0 ≠ none := by blaster
example : constrDataAt .defaultFunSemanticsVariantD word64Max ≠ none := by blaster
example : constrDataAt .defaultFunSemanticsVariantD (-1) = none := by blaster
example : constrDataAt .defaultFunSemanticsVariantD (word64Max + 1) = none := by blaster

-- The same under E.
example : constrDataAt .defaultFunSemanticsVariantE 0 ≠ none := by blaster
example : constrDataAt .defaultFunSemanticsVariantE word64Max ≠ none := by blaster
example : constrDataAt .defaultFunSemanticsVariantE (-1) = none := by blaster
example : constrDataAt .defaultFunSemanticsVariantE (word64Max + 1) = none := by blaster

-- Before protocol version 11 (B for V1/V2, C for V3) indices outside that range
-- are accepted.
example : constrDataAt .defaultFunSemanticsVariantB (-1) ≠ none := by blaster
example : constrDataAt .defaultFunSemanticsVariantB (word64Max + 1) ≠ none := by blaster
example : constrDataAt .defaultFunSemanticsVariantC (-1) ≠ none := by blaster
example : constrDataAt .defaultFunSemanticsVariantC (word64Max + 1) ≠ none := by blaster

end Tests.Issue33
