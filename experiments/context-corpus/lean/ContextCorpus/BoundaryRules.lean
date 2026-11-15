import Blaster.Optimize.Basic
import ContextCorpus.Boundary

namespace ContextCorpus

/-- This rule tests whether PR472 sees a local validity consequence before
    preparing the CEK call. It does not establish the full validity contract. -/
@[blaster]
theorem rawArgs_of_shape (d : PlutusCore.Data.Data) (h : WellShaped d) :
    rawArgs d = viewArgs (viewOf d) := by
  unfold viewArgs
  rw [encode_viewOf d h]

def assumedArgs (d : PlutusCore.Data.Data) (_h : WellShaped d) :
    List PlutusCore.UPLC.Term.Term := rawArgs d

end ContextCorpus
