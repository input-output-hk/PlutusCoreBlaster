import PlutusCore.UPLC.Optimize.ScalarSearch
import PlutusCore.UPLC.PlutusScript

/-! Complete UPLC programs using different predicates and result consumers.
    The search recognizer sees their resulting CEK states, not these names. -/
namespace Tests.GenericOptimizationFixture
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.Optimize.ScalarSearch
open PlutusCore.Data (Data)

def search (p : Predicate) : Term :=
  let code := body ⟨3, 2, 1, 0⟩ (p.test 1)
  let self := Term.Lam (.Lam code)
  .Apply (.Apply self self) (.Var 4)

def bindBuiltins (code : Term) : Term :=
  let withTail := Term.Apply (.Lam code) (.Force (.Builtin .TailList))
  let withHead := Term.Apply (.Lam withTail) (.Force (.Builtin .HeadList))
  let withChoose := Term.Apply (.Lam withHead) (.Force (.Force (.Builtin .ChooseList)))
  .Apply (.Lam withChoose) (.Force (.Builtin .IfThenElse))

def program (p : Predicate) (consumer : Term → Term) : Program :=
  .Program (.Version 1 1 0) (.Lam (bindBuiltins (consumer (search p))))

def guard (result : Term) : Term :=
  .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) result)
    (.Delay (.Const .Unit))) (.Delay .Error))

def integerMember : PlutusScript := ⟨.PlutusV3, program (.integer .eq 7) id⟩
def bytesMember : PlutusScript := ⟨.PlutusV3, program (.bytes .eq ⟨"abc"⟩) id⟩
def integerThreshold : PlutusScript := ⟨.PlutusV3, program (.integer .lt 10) guard⟩

def params (xs : List Data) : List Term := [.Const (.ConstDataList xs)]

end Tests.GenericOptimizationFixture
