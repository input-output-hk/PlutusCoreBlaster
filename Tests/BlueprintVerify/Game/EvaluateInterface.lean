import PlutusCore.UPLC.BlueprintEncoding.Basic
import PlutusCore.UPLC.Utils
#import_blueprints Game "Tests/BlueprintVerify/Game/plutus.json"
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term Const)
open PlutusCore.UPLC.CekMachine
open PlutusCore.Default.Internal (BuiltinSemanticsVariant)

def runGame (d r c : Data) :=
  cekExecuteProgramWithSemanticVariant BuiltinSemanticsVariant.defaultFunSemanticsVariantD
    Game.gameValidator.script [Term.Const (Const.Data d), Term.Const (Const.Data r), Term.Const (Const.Data c)] 500

-- SHA-256 is opaque to SMT. This is a separate execution test of a known vector.
def secretHash : ByteString :=
  { data := String.mk (([44,242,77,186,95,176,163,14,38,232,59,42,197,185,226,158,27,22,30,92,31,167,66,94,115,4,51,98,147,139,152,36] : List Nat).map Char.ofNat) }

#eval show IO Unit from do
  match runGame (Data.B secretHash) (Data.B { data := "hello" }) (Data.I 0) with
  | .Halt (.VCon .Unit) => pure ()
  | _ => throw (IO.userError "matching SHA-256 vector did not return unit")
  match runGame (Data.B secretHash) (Data.B { data := "wrong" }) (Data.I 0) with
  | .Error => pure ()
  | _ => throw (IO.userError "nonmatching SHA-256 vector did not fail")
