import PlutusCore.UPLC.Optimize.Composition
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

attribute [blaster] Composition.execute_empty Composition.execute_identity
  Composition.execute_constant Composition.execute_assert
attribute [blaster] Composition.conditional_tail

end PlutusCore.UPLC.Optimize
