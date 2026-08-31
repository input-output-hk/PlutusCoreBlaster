import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.PlutusScript
import PlutusCore.UPLC.ScriptEncoding.Basic

/-- A variant of `#import_uplc` for conformance parse-error tests.
    Behaves identically on success; on any parse failure emits a fixed
    `"Parsing error"` message instead of the verbose diagnostic. -/
syntax (name := conformanceImportUplc) "#conformance_import_uplc" ident str : command

open Lean Elab Command Term in
@[command_elab conformanceImportUplc]
def conformanceImportUplcImpl : CommandElab := fun stx => do
  let declName := stx[1].getId
  let path ←
    match stx[2].isStrLit? with
    | some x => pure x
    | none   => throwError "empty path"
  -- Read the file; any IO error counts as a parse error
  let content ← try IO.FS.readFile path catch _ => throwError "Parsing error"
  -- Parse the UPLC text; any parse error emits the standard message
  let prog ←
    match PlutusCore.UPLC.TextEncoding.programFromString content with
    | .ok p    => pure p
    | .error _ => throwError "Parsing error"
  logInfo s!"Successfully decoded textual '{path}'"
  -- Register the definition exactly as #import_uplc does
  let decl ← runTermElabM fun _ => do
    let progExpr := Lean.toExpr prog
    let t ← Meta.inferType progExpr
    return Declaration.defnDecl {
      name        := declName
      levelParams := []
      type        := t
      value       := progExpr
      hints       := .abbrev
      safety      := .safe
    }
  liftCoreM <| addAndCompile decl

namespace Tests.Conformance

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.ExBudget
open PlutusCore.Default

-- Needed so that partial defs returning Term can compile in the mutual block below.
private instance : Inhabited Term := ⟨.Error⟩

-- The helpers live in one mutual block so that cekValueBeq can call
-- closeTermWithEnv without forward-reference issues.
--
-- VLam and VDelay close their bodies using their environments before
-- comparing, so closures that differ only in how the environment is
-- folded into the body still compare as equal. With de Bruijn indices,
-- comparison of the closed terms is plain structural equality (BEq Term),
-- which ignores display-only binder names.
mutual
  -- Convert a CekValue back to a Term for substitution.
  private def cekValueToTerm : Nat → CekValue → Term
    | p + 1, .VCon c            => .Const c
    | p + 1, .VLam x body env   => .Lam x (closeTermWithEnv env 1 p body)
    | p + 1, .VDelay body env   => .Delay (closeTermWithEnv env 0 p body)
    | p + 1, .VConstr n args    => .Constr n (args.map (cekValueToTerm p))
    | p + 1, .VBuiltin f args _ => args.foldr (fun v acc => .Apply acc (cekValueToTerm p v)) (.Builtin f)
    | 0    , _                  => .Error

  -- Close a Term by substituting variables that reach past the `depth`
  -- enclosing binders from `env`. Substituted values are closed recursively,
  -- so no index shifting is needed.
  private def closeTermWithEnv (env : Environment) (depth : Nat) : Nat → Term → Term
    | p + 1, .Var i =>
        if i < depth then .Var i
        else match env[i - depth]? with
             | some v => cekValueToTerm p v
             | none   => .Var i
    | p + 1, .Lam x body  => .Lam x (closeTermWithEnv env (depth + 1) p body)
    | p + 1, .Apply f a   => .Apply (closeTermWithEnv env depth p f) (closeTermWithEnv env depth p a)
    | p + 1, .Delay t     => .Delay (closeTermWithEnv env depth p t)
    | p + 1, .Force t     => .Force (closeTermWithEnv env depth p t)
    | p + 1, .Constr n ts => .Constr n (ts.map (closeTermWithEnv env depth p))
    | p + 1, .Case s hs   => .Case (closeTermWithEnv env depth p s) (hs.map (closeTermWithEnv env depth p))
    | _    , t            => t

  private def cekValueBeq : Nat → CekValue → CekValue → Bool
    | _    , .VCon c1,              .VCon c2              => c1 == c2
    | p + 1, .VConstr n1 args1,     .VConstr n2 args2     => n1 == n2 && cekValueListBeq p args1 args2
    | p + 1, .VBuiltin f1 args1 _,  .VBuiltin f2 args2 _  => f1 == f2 && cekValueListBeq p args1 args2
    | p + 1, .VLam _ t1 env1,       .VLam _ t2 env2       =>
        closeTermWithEnv env1 1 p t1 == closeTermWithEnv env2 1 p t2
    | p + 1, .VDelay t1 env1,       .VDelay t2 env2       =>
        closeTermWithEnv env1 0 p t1 == closeTermWithEnv env2 0 p t2
    | _    , _              , _                           => false

  private def cekValueListBeq : Nat → List CekValue → List CekValue → Bool
    | p + 1, x :: xs, y :: ys => cekValueBeq p x y && cekValueListBeq p xs ys
    | _    , [],      []      => true
    | _    , _      , _       => false
end

/-- A large step budget used for conformance test value evaluation.
    Set high enough that no conformance test should exhaust it. -/
def conformanceSteps : Nat := 10_000_000_000

/-- Int64 max; Haskell's budget arithmetic saturates at this value. -/
def int64Max : Nat := 9223372036854775807

/-- A large ExBudget used for conformance test budget evaluation.
    Must exceed any single-step cost that Haskell's Int64 arithmetic saturates
    (e.g. DropList with a very large n can cost ~2×10²² before saturation). -/
def conformanceMaxBudget : ExBudget :=
  { exBudgetCPU    := { unExCPU    := 100_000_000_000_000_000_000_000_000 }
  , exBudgetMemory := { unExMemory := 100_000_000_000_000_000_000_000_000 } }

/-- Check whether two programs evaluate to the same CekValue.
    Uses the step-limited evaluator with PlutusV3 semantics.
    Returns true iff both evaluate to the same ground value (or both error). -/
def programsEvalEquiv (p1 p2 : PlutusScript) : Bool :=
  match cekExecuteProgram p1.script [] conformanceSteps,
        cekExecuteProgram p2.script [] conformanceSteps with
  | State.Halt v1, State.Halt v2 => cekValueBeq conformanceSteps v1 v2
  | State.Error,   State.Error   => true
  | _,             _             => false

/-- Check whether a program evaluates to an error (evaluation failure). -/
def programEvalsToError (p : PlutusScript) : Bool :=
  match cekExecuteProgram p.script [] conformanceSteps with
  | State.Error => true
  | _           => false

/-- Check whether a program's cpu and memory budget matches the expected values.
    Uses PlutusV3 post-Van-Rossem semantics, which matches the conformance test defaults. -/
def budgetMatches (p : PlutusScript) (expectedCpu expectedMem : Nat) : Bool :=
  match cekExecuteProgramWithBudget p.script .plutusV3 .postVanRossem [] conformanceMaxBudget with
  | EvaluationResult.Success _ b =>
      -- Haskell uses Int64 saturation arithmetic: costs exceeding Int64.max
      -- saturate to Int64.max rather than overflowing. Apply the same cap here.
      let actualCpu := min b.exBudgetCPU.unExCPU       int64Max
      let actualMem := min b.exBudgetMemory.unExMemory int64Max
      actualCpu == expectedCpu && actualMem == expectedMem
  | _ => false

end Tests.Conformance
