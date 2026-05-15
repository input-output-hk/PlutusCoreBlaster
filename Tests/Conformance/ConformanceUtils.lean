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

-- Look up a variable in an Environment (most-recent binding wins).
private def envLookup : Environment → String → Option CekValue
  | .EmptyEnvironment            , _ => none
  | .NonEmptyEnvironment rest k v, x => if k == x then some v else envLookup rest x

-- All six helpers live in one mutual block so that cekValueBeq can call
-- closeTermWithEnv and alphaEqWith without forward-reference issues.
--
-- VLam and VDelay close their bodies using their environments before
-- alpha-comparing, so closures that differ only in how the environment
-- is folded into the body still compare as equal.
mutual
  -- Alpha-equivalence for Terms.
  -- ctx is a stack of (name-in-t1, name-in-t2) pairs introduced by binders we've descended into.
  -- Free variables must match by name; bound variables match by position.
  private def alphaEqWith (ctx : List (String × String)) : Term → Term → Bool
    | .Var x,         .Var y         =>
        match ctx.find? (fun p => p.1 == x) with
        | some (_, z) => z == y
        | none        => x == y
    | .Lam x b1,      .Lam y b2      => alphaEqWith ((x, y) :: ctx) b1 b2
    | .Apply f1 a1,   .Apply f2 a2   => alphaEqWith ctx f1 f2 && alphaEqWith ctx a1 a2
    | .Delay t1,      .Delay t2      => alphaEqWith ctx t1 t2
    | .Force t1,      .Force t2      => alphaEqWith ctx t1 t2
    | .Const c1,      .Const c2      => c1 == c2
    | .Builtin b1,    .Builtin b2    => b1 == b2
    | .Constr n1 ts1, .Constr n2 ts2 => n1 == n2 && alphaEqListWith ctx ts1 ts2
    | .Case s1 hs1,   .Case s2 hs2   => alphaEqWith ctx s1 s2 && alphaEqListWith ctx hs1 hs2
    | .Error,         .Error         => true
    | _,              _              => false

  private def alphaEqListWith (ctx : List (String × String)) : List Term → List Term → Bool
    | [],      []      => true
    | t :: ts, u :: us => alphaEqWith ctx t u && alphaEqListWith ctx ts us
    | _,       _       => false
end

mutual
  -- Convert a CekValue back to a Term for substitution.
  private def cekValueToTerm : Nat → CekValue → Term
    | p + 1, .VCon c            => .Const c
    | p + 1, .VLam x body env   => .Lam x (closeTermWithEnv env [x] p body)
    | p + 1, .VDelay body env   => .Delay (closeTermWithEnv env []  p body)
    | p + 1, .VConstr n args    => .Constr n (args.map (cekValueToTerm p))
    | p + 1, .VBuiltin f args _ => args.foldr (fun v acc => .Apply acc (cekValueToTerm p v)) (.Builtin f)
    | 0    , _                  => .Error

  -- Close a Term by substituting free variables (not in `bound`) from `env`.
  private def closeTermWithEnv (env : Environment) (bound : List String) : Nat → Term → Term
    | p + 1, .Var x =>
        if bound.contains x then .Var x
        else match envLookup env x with
             | some v => cekValueToTerm p v
             | none   => .Var x
    | p + 1, .Lam x body  => .Lam x (closeTermWithEnv env (x :: bound) p body)
    | p + 1, .Apply f a   => .Apply (closeTermWithEnv env bound p f) (closeTermWithEnv env bound p a)
    | p + 1, .Delay t     => .Delay (closeTermWithEnv env bound p t)
    | p + 1, .Force t     => .Force (closeTermWithEnv env bound p t)
    | p + 1, .Constr n ts => .Constr n (ts.map (closeTermWithEnv env bound p))
    | p + 1, .Case s hs   => .Case (closeTermWithEnv env bound p s) (hs.map (closeTermWithEnv env bound p))
    | _    , t            => t

  private def cekValueBeq : Nat → CekValue → CekValue → Bool
    | _    , .VCon c1,              .VCon c2              => c1 == c2
    | p + 1, .VConstr n1 args1,     .VConstr n2 args2     => n1 == n2 && cekValueListBeq p args1 args2
    | p + 1, .VBuiltin f1 args1 _,  .VBuiltin f2 args2 _  => f1 == f2 && cekValueListBeq p args1 args2
    | p + 1, .VLam x1 t1 env1,      .VLam x2 t2 env2      =>
        alphaEqWith [(x1, x2)] (closeTermWithEnv env1 [x1] p t1) (closeTermWithEnv env2 [x2] p t2)
    | p + 1, .VDelay t1 env1,       .VDelay t2 env2       =>
        alphaEqWith [] (closeTermWithEnv env1 [] p t1) (closeTermWithEnv env2 [] p t2)
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
    Uses PlutusV3 post-Conway semantics, which matches the conformance test defaults. -/
def budgetMatches (p : PlutusScript) (expectedCpu expectedMem : Nat) : Bool :=
  match cekExecuteProgramWithBudget p.script .plutusV3 .postConway [] conformanceMaxBudget with
  | EvaluationResult.Success _ b =>
      -- Haskell uses Int64 saturation arithmetic: costs exceeding Int64.max
      -- saturate to Int64.max rather than overflowing. Apply the same cap here.
      let actualCpu := min b.exBudgetCPU.unExCPU       int64Max
      let actualMem := min b.exBudgetMemory.unExMemory int64Max
      actualCpu == expectedCpu && actualMem == expectedMem
  | _ => false

end Tests.Conformance
