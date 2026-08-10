import PlutusCore.UPLC.CekMachine
import PlutusCore.Default

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/32
--
-- `case` on a scrutinee that reduces to a plain constant (as opposed to a
-- `constr` value) is only valid from the Van Rossem hard fork onward; older
-- protocol versions must reject it the same as if `case`-on-constants didn't
-- exist.
namespace Tests.Issue32

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.CekMachine
open PlutusCore.Default

-- `case 0 [111, 222]` -- Case scrutinizing a bare Integer constant, not a
-- `constr` value; should select branch 0.
def caseOnConstantProgram : Program :=
  Program.Program (Version.Version 1 1 0)
    (Term.Case (Term.Const (Const.Integer 0))
      [Term.Const (Const.Integer 111), Term.Const (Const.Integer 222)])

example :
    (match cekExecuteProgramWithSemanticVariant default .preConway caseOnConstantProgram [] 10 with
     | State.Error => true
     | _ => false) = true := by
  native_decide

example :
    (match cekExecuteProgramWithSemanticVariant default .postConwayPreVanRossem caseOnConstantProgram [] 10 with
     | State.Error => true
     | _ => false) = true := by
  native_decide

example :
    (match cekExecuteProgramWithSemanticVariant default .postVanRossem caseOnConstantProgram [] 10 with
     | State.Halt (CekValue.VCon (Const.Integer n)) => n == 111
     | _ => false) = true := by
  native_decide

end Tests.Issue32
