import PlutusCore.UPLC.Optimize.Administrative
import Blaster.Optimize.Basic

namespace PlutusCore.UPLC.Optimize
open Lean Meta
open Blaster.Optimize
open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.Data (Data)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

attribute [blaster] Administrative.apply_lambda Administrative.force_delay
  Administrative.return_lambda Administrative.return_lambda_left
  Administrative.lookup_tail Administrative.lookup_head Administrative.return_empty

end PlutusCore.UPLC.Optimize
