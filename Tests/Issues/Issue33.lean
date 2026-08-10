import PlutusCore.UPLC.BuiltinFunctions.Data

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/33
--
-- Since semantics variant D (Conway/PlutusV3 onward), `ConstrData`'s
-- constructor-index argument must fit in a Word64; out-of-range indices
-- must fail the builtin rather than being silently accepted. Variants A/B/C
-- keep accepting any Integer, matching pre-Conway behaviour.
namespace Tests.Issue33

open PlutusCore.UPLC.BuiltinFunctions.Data
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term (Const)

-- 2^64, i.e. one past Word64's maximum representable value.
private def outOfRangeIndex : PlutusCore.Integer.Integer := 18446744073709551616

example :
    (match constrData .defaultFunSemanticsVariantD
       [CekValue.VCon (Const.ConstDataList []), CekValue.VCon (Const.Integer outOfRangeIndex)] with
     | none => true
     | some _ => false) = true := by
  native_decide

example :
    (match constrData .defaultFunSemanticsVariantE
       [CekValue.VCon (Const.ConstDataList []), CekValue.VCon (Const.Integer (-1))] with
     | none => true
     | some _ => false) = true := by
  native_decide

example :
    (match constrData .defaultFunSemanticsVariantC
       [CekValue.VCon (Const.ConstDataList []), CekValue.VCon (Const.Integer outOfRangeIndex)] with
     | some _ => true
     | none => false) = true := by
  native_decide

example :
    (match constrData .defaultFunSemanticsVariantD
       [CekValue.VCon (Const.ConstDataList []), CekValue.VCon (Const.Integer 5)] with
     | some _ => true
     | none => false) = true := by
  native_decide

end Tests.Issue33
