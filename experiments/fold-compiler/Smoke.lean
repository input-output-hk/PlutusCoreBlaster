import PlutusCore.UPLC.Optimize.CallbackCompiler
open Lean Meta Elab Command Term
open PlutusCore.UPLC.Optimize PlutusCore.UPLC.Optimize.CompiledFold
open PlutusCore.UPLC.Term PlutusCore.UPLC.CekValue
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace FoldCompilerSmoke
-- The same compiler handles raw elements and key/value pairs; no field names.
def bindings : Bindings where
 env := [.VBuiltin .ChooseList [] (.More .ArgV (.More .ArgV (.One .ArgV))),
   .VBuiltin .TailList [] (.One .ArgV), .VBuiltin .HeadList [] (.One .ArgV),
   .VBuiltin .SndPair [] (.One .ArgV)]
 chooseIndex := 0
 tailIndex := 1
 chooseBound := rfl
 tailBound := rfl

def sumData : PlutusCore.UPLC.Term.Term :=
 .Apply (.Apply (.Builtin .AddInteger) (.Var 0))
   (.Apply (.Builtin .UnIData) (.Apply (.Var 5) (.Var 1)))
def sumPairs : PlutusCore.UPLC.Term.Term :=
 .Apply (.Apply (.Builtin .AddInteger) (.Var 0))
   (.Apply (.Builtin .UnIData) (.Apply (.Var 6) (.Apply (.Var 5) (.Var 1))))
-- A singleton execution cannot justify reading the second list element.
def tailDependent : PlutusCore.UPLC.Term.Term :=
 .Apply (.Builtin .UnIData) (.Apply (.Var 5) (.Apply (.Var 4) (.Var 1)))

run_cmd do
 runTermElabM fun _ => do
  let binding ← reduce (← elabTermAndSynthesize (← `(bindings)) none)
  let sem ← elabTermAndSynthesize (← `((default : PlutusCore.Default.BuiltinSemanticsVariant))) none
  for (kindSyntax, codeSyntax) in [(← `(Kind.data), ← `(sumData)), (← `(Kind.pair), ← `(sumPairs))] do
   let kind ← elabTermAndSynthesize kindSyntax none
   let callback ← reduce (← elabTermAndSynthesize codeSyntax none)
   let compiled ← CallbackCompiler.compile kind binding callback sem
   let _ ← inferType compiled
   logInfo "callback compiled and kernel checked"
  let saved ← saveState
  let mut declined := false
  try
   let kind ← elabTermAndSynthesize (← `(Kind.data)) none
   let callback ← reduce (← elabTermAndSynthesize (← `(tailDependent)) none)
   let _ ← CallbackCompiler.compile kind binding callback sem
  catch _ => declined := true
  saved.restore
  unless declined do throwError "tail-dependent callback was accepted"
  logInfo "tail-dependent callback declined"

#print axioms CompiledFold.run_summary
end FoldCompilerSmoke
