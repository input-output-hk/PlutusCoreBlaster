import PlutusCore.UPLC.BuiltinFunctions.List
import PlutusCore.UPLC.CekValue

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/37
--
-- `mkCons` must reject consing an element of the wrong shape onto a
-- non-empty `ConstList`, matching Haskell's builtin type-tag check. Args are
-- reversed on the Cek machine stack: `[existingList, newElement]`.
namespace Tests.Issues.Issue37

open PlutusCore.UPLC.BuiltinFunctions.List
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term (Const)

-- Consing a Bool onto a non-empty list(integer) must fail.
example :
    (match mkCons
       [ CekValue.VCon (Const.ConstList [Const.Integer 1, Const.Integer 2])
       , CekValue.VCon (Const.Bool true) ] with
     | none => true
     | some _ => false) = true := by
  native_decide

-- Consing an Integer onto a non-empty list(integer) must still succeed.
example :
    (match mkCons
       [ CekValue.VCon (Const.ConstList [Const.Integer 1, Const.Integer 2])
       , CekValue.VCon (Const.Integer 3) ] with
     | some (CekValue.VCon (Const.ConstList [Const.Integer 3, Const.Integer 1, Const.Integer 2])) => true
     | _ => false) = true := by
  native_decide

-- Consing onto an empty list is still accepted unconditionally: the
-- declared element type isn't retained once the list is empty, so this
-- case can't be checked without a representation change (see issue #37).
example :
    (match mkCons
       [ CekValue.VCon (Const.ConstList []), CekValue.VCon (Const.Bool true) ] with
     | some _ => true
     | none => false) = true := by
  native_decide

end Tests.Issues.Issue37
