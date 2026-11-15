import Blaster.Optimize.Basic

namespace ContextCorpus
open Lean Meta Blaster.Optimize

/-- Experimental preparation entry point: keep proof parameters in scope and
    explicitly seed PR472's hypothesis map before optimizing the body. Merely
    putting a proof parameter on an input conversion does not do this in the
    currently pinned optimizer. No global optimizer implementation is changed. -/
def optimizeUnderAssumptions (e : Expr) : MetaM Expr :=
  lambdaTelescope e fun parameters body => do
    let action : TranslateEnvT Expr := do
      updateLocalContext (← mkLocalContext)
      for decl in (← getLCtx) do
        if ← isProp decl.type then
          let _ ← addHypotheses (← hashcons decl.type) (mkFVar decl.fvarId)
      Optimize.mainAux body
    let (result, _) ← action.run default
    mkLambdaFVars parameters result

end ContextCorpus
