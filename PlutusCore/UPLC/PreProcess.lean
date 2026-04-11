import Lean
import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.PlutusScript
import Blaster.Optimize.Basic
open Lean Elab Command Term Meta Blaster.Optimize

namespace PlutusCore.UPLC.PreProcess
open CekMachine
open PlutusScript
open Term

/--
 `#prep_uplc` is a Lean4 command that accepts a `PlutusScript` instance as argument,
  optimizes the uplc program in `PlutusScript.script` according to the provided script budget
  and generates a `PrepUPLC.xxx` instance such that:
    { lang := PlutusScript.lang
    , prop := <optimized uplc code w.r.t. the cex machine for formal proof>
    , exec := <executable uplc code w.r.t. the cex machine>
    }

    The #prep_uplc usage is as follows:
     #prep_uplc <new-identifier> <plutus-script-instance> (input-conversion-function)? UNIT

    E.g. `#prep_uplc compiledProcessSCOrder processSCOrder orderInputToParams 500`
-/

syntax uplcMaxSteps := num
syntax (name := preprocess) "#prep_uplc" ident ident (ident)? uplcMaxSteps : command

def parseMaxSteps : TSyntax `uplcMaxSteps → TermElabM Nat
  | `(uplcMaxSteps | $n:num) => return n.getNat
  | _ => throwUnsupportedSyntax

@[command_elab preprocess]
def preprocessImp : CommandElab := fun stx => do
  let (propDecl, execDecl, structDef, structDescr, structInst) ←
      withoutModifyingEnv $ runTermElabM fun _ => do
        let plutusScript ← validUplcProg stx[2]
        let app ← mkUplcApply stx plutusScript
        let (e, _) ← Optimize.main app|>.run default
        let t ← inferType e
        let baseName ← validNewDef stx[1]
        let propName := Name.append baseName `prop
        let execName := Name.append baseName `exec
        let propDef := createDefinition propName t e
        let execDef := createDefinition execName t app
        let structName := Name.append `PrepUPLC baseName
        let structCtor := Name.append structName `mk
        let (structDef, structDescr) := createStructure structName structCtor t
        let structInst :=
          Declaration.defnDecl {
            name := baseName
            levelParams := [],
            type := mkConst structName,
            value := mkApp3 (mkConst structCtor) (← whnf $ mkProj ``PlutusScript 0 plutusScript) e app,
            hints := .abbrev,
            safety := .safe }
        return (propDef, execDef, structDef, structDescr, structInst)
  modifyEnv (addNoncomputable · propDecl.definitionVal!.name)
  liftCoreM <| addDecl propDecl
  liftCoreM <| addAndCompile execDecl
  liftCoreM <| addAndCompile structDef
  liftCoreM <| modifyEnv (λ env => registerStructure env structDescr)
  modifyEnv (addNoncomputable · structInst.definitionVal!.name)
  liftCoreM <| addDecl structInst

  where
    createDefinition (n : Name) (t : Expr) (e : Expr) : Declaration :=
      Declaration.defnDecl {
       name := n,
       levelParams := [],
       type := t,
       value := e,
       hints := .abbrev,
       safety := .safe }

    createStructure (structName : Name) (structCtor : Name) (t : Expr) : (Declaration × StructureDescr) :=
      let ctor : Constructor := {
         name := structCtor,
         type :=
           mkForall `lang .default (mkConst ``PlutusLanguage) $
           mkForall `prop .default t $
           mkForall `exec .default t $
           mkConst structName
      }
      let indType : InductiveType :=
        { name := structName,
          type := mkSort levelOne,
          ctors := [ctor]
        }
      let mkFieldInfo (field : Name) : StructureFieldInfo :=
         { fieldName := field,
           projFn := Name.append structName field,
           subobject? := none,
           binderInfo := .default,
           autoParam? := none
         }
      let descr : StructureDescr := {
        structName := structName,
        fields := #[ mkFieldInfo `lang, mkFieldInfo `prop, mkFieldInfo `exec ]
      }
      let decl := Declaration.inductDecl [] 0 [indType] false
      (decl, descr)

    validNewDef (f : Syntax) : TermElabM Name := return f.getId

    /-- Resolve prog ident and validate that it
        corresponds to a definition returning UPLC.Term.Program.
    -/
    validUplcProg (prog : Syntax) : TermElabM Expr := do
      let some uplcProg ← resolveId? prog |
        throwErrorAt prog m!"unknown constant '{.ofConstName prog.getId}'"
      let ConstantInfo.defnInfo info ← getConstInfo uplcProg.constName! |
        throwErrorAt prog m!"unknown definition '{.ofConstName prog.getId}'"
      let Expr.const ``PlutusScript _ := info.type |
        throwErrorAt prog m!"PlutusScript type expected for '{.ofConstName prog.getId}'"
      return uplcProg

    validFunType (t : Expr) : TermElabM Bool := do
      Meta.forallTelescope t fun xs ret =>
        match ret with
        | Expr.app (Expr.const ``List _) (Expr.const ``UPLC.Term.Term _) => return true
        | _ => return false

    /-- Resolve input conversion function `f` and ensures that:
       - Type(f) = α₁ → .. → αₙ → List UPLC.Term.Term`
       NOTE: that Type(f) can also be `List UPLC.Term.Term` only, i.e.,
       f produces constant uplc values.
    -/
    validConversionFun (f : Syntax) : TermElabM (Option Expr) := do
      match f.getOptional? with
      | none => return none
      | some f' =>
         let some conv ← resolveId? f' |
           throwErrorAt f' m!"unknown constant '{.ofConstName f'.getId}'"
         let ConstantInfo.defnInfo info ← getConstInfo conv.constName! |
           throwErrorAt f' m!"unknown definition '{.ofConstName f'.getId}'"
         if !(← validFunType info.type) then
           throwErrorAt f' m!"invalid input conversion fun type '{info.type}'"
         return conv

    mkUplcApply (stx : Syntax) (plutusScript : Expr) : TermElabM Expr := do
      let unit ← parseMaxSteps ⟨stx[4]⟩
      -- validate that Type(f) := α₁ → .. → αₙ → List Term` ∧
      --  ∀ i ∈ [1..inputs.size], Type(inputs[i]!) = αᵢ
      let cekExec := Lean.mkConst ``cekExecuteProgram
      let termType := Lean.mkConst ``UPLC.Term.Term
      let uplcProg := mkProj ``PlutusScript 1 plutusScript
      match (← validConversionFun stx[3]) with
      | none => return mkApp3 cekExec uplcProg (mkApp (Lean.mkConst ``List.nil) termType) (mkNatLit unit)
      | some f =>
           Meta.lambdaTelescope (← Meta.etaExpand f) fun xs _ =>
             mkLambdaFVars xs (mkApp3 cekExec uplcProg (mkAppN f xs) (mkNatLit unit))

end PlutusCore.UPLC.PreProcess
