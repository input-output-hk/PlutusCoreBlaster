import Tests.Conformance.ConformanceUtils
import PlutusCore.UPLC.CostModels
import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.ScriptEncoding.Basic
open Tests.Conformance
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.ExBudget
open PlutusCore.Default
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CostModels

-- Directly test the cost function on expected args (forward order):
-- args[0]=Bool False, args[1]=Integer 12, args[2]=Integer 0
#eval!
  let args : List CekValue := [.VCon (.Bool false), .VCon (.Integer 12), .VCon (.Integer 0)]
  builtinCostsC .IntegerToByteString args
