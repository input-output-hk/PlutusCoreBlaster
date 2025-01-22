
namespace PlutusCore.Trace

/-! ## Formalisation for PlutusCore trace builtin function. -/

/-- Given `s` and `a` always return `a`. -/
def trace (_s : String) (a : α) : α := a

end PlutusCore.Trace
