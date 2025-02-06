import PlutusCore.Trace.Basic

namespace PlutusCore.Trace

/-! ## Theorems on PlutusCore trace builtin function. -/
@[simp] theorem trace_rfl (s : String) (a : α) : trace s a = a := rfl

end PlutusCore.Trace
