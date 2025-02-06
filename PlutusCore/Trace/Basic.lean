
namespace PlutusCore.Trace

/-! ## Formalisation for PlutusCore trace builtin function. -/

namespace PlutusCore.TraceInternal
/-- Given `s` and `a` always return `a`. -/
def trace (_s : String) (a : α) : α := a

end PlutusCore.TraceInternal

export PlutusCore.TraceInternal
  ( -- builtin function
    trace
  )

end PlutusCore.Trace
