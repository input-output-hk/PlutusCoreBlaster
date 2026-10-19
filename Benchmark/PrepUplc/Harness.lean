import Lean
import Std.Internal.UV.System
import PlutusCore.UPLC.PreProcess
import PlutusCore.UPLC.ScriptEncoding.Basic

/-!
# `#prep_uplc` benchmark harness

Two commands elaborate a single `#prep_uplc` and measure it:

* `#bench_prep_uplc "<id>" <script> (<conversion-fn>)? <max-steps>`
  where `<script>` is a `PlutusScript` or a `Program` constant;
* `#bench_prep_uplc_file "<id>" <lang> <format> "<path>" (<conversion-fn>)? <max-steps>`
  which first imports the script like `#import_uplc` does (`<format>` can also be `auto`).

The `#prep_uplc` command is measured alone: importing or wrapping the script, and the checks
below, happen outside the measured region. For a closed program (no conversion function, or one
that takes no arguments), the
harness also runs `cekExecuteProgram` natively, apart from `#prep_uplc`: it times that run and
records how it ends and how many machine steps it takes. The measured command runs with
`Elab.async` off, so that the kernel checks and compilation triggered by its `addDecl`s happen
inside the measured region instead of in background tasks, and with `maxHeartbeats` 0.
Heartbeats are not reported: the Blaster optimizer resets the counter while it runs.

Each measurement is appended as one JSON line to the file named by the environment variable
`PREP_UPLC_BENCH_OUT` (when set), and summarized in an info message.
-/

namespace Benchmark.PrepUplc

open Lean Elab Command
open PlutusCore.UPLC.CekMachine (step initialState applyParams)
open PlutusCore.UPLC.PlutusScript (PlutusScript PlutusLanguage)
open PlutusCore.UPLC.Term (Program)

register_option bench.prepUplc.runs : Nat := {
  defValue := 1
  descr    := "number of times `#bench_prep_uplc` runs `#prep_uplc`, each time on a fresh copy of the environment"
}

/-- The `PlutusScript` given to `#prep_uplc` when the benchmark has to create one. -/
def scriptName : Name := `bench_prep_uplc_script

/-- The declarations created by the measured `#prep_uplc`. -/
def resultName : Name := `bench_prep_uplc_result

/-! ## Process statistics -/

/-- Resident set size and its peak (`VmRSS` and `VmHWM`), in kB. Linux only. -/
structure ProcMem where
  rssKb : Nat
  hwmKb : Nat

def readProcMem? : IO (Option ProcMem) := do
  let status ← try IO.FS.readFile "/proc/self/status" catch _ => return none
  let field (key : String) : Option Nat :=
    (status.splitOn "\n").findSome? (λ line =>
      if line.startsWith key then ((line.drop key.length).trim.takeWhile Char.isDigit).toNat?
      else none)
  return do return { rssKb := ← field "VmRSS:", hwmKb := ← field "VmHWM:" }

/-- Resets `VmHWM` to the current resident set size (Linux ≥ 4.0), so that it records the
    peak of what follows. -/
def resetPeakRss : IO Unit :=
  try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()

/-- CPU time (user + system) of the process in ms, and its lifetime peak RSS in kB. -/
def rusage : IO (Nat × Nat) := do
  let r ← Std.Internal.UV.System.getrusage
  return ((r.userTime + r.systemTime).toNat, r.maxRSS.toNat)

/-- `ms` with one decimal. -/
def fmtMs (ms : Float) : String :=
  let tenths := (ms * 10).round.toUInt64.toNat
  s!"{tenths / 10}.{tenths % 10}"

/-- One measured elaboration of `#prep_uplc`. -/
structure Run where
  wallNs      : Nat
  cpuMs       : Nat
  rssBeforeKb : Option Nat
  /-- Peak RSS during the run; the lifetime peak of the process when `/proc` is unavailable. -/
  peakRssKb   : Nat
  rssAfterKb  : Option Nat

def Run.wallMs (r : Run) : Float := r.wallNs.toFloat / 1e6

def Run.peakDeltaKb? (r : Run) : Option Nat := r.rssBeforeKb.map (r.peakRssKb - ·)

def Run.report (r : Run) : Json :=
  Json.mkObj
  [ ("wall_ms"      , toJson r.wallMs)
  , ("cpu_ms"       , toJson r.cpuMs)
  , ("rss_before_kb", toJson r.rssBeforeKb)
  , ("peak_rss_kb"  , toJson r.peakRssKb)
  , ("rss_after_kb" , toJson r.rssAfterKb)
  ]

/-! ## Elaboration helpers -/

/-- Runs a benchmark command: with the options every benchmarked command runs with, and without
    keeping any of its declarations, so that one file can hold several benchmarks. -/
def withBenchOptions (x : CommandElabM α) : CommandElabM α :=
  withScope (λ sc => { sc with opts := sc.opts.setBool `Elab.async false |>.setNat `maxHeartbeats 0 })
    (withoutModifyingEnv x)

/-- Parses a command, dropping its positions so that its messages point at the benchmark command. -/
def parseCommand (text : String) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .ok stx    => return stx.rewriteBottomUp (·.setInfo .none)
  | .error msg => throwError "failed to parse `{text}`: {msg}"

/-- Elaborates `stx` and returns the errors it logged. -/
def elabCollectingErrors (stx : Syntax) : CommandElabM (Array Message) := do
  let n := (← get).messages.toArray.size
  elabCommand stx
  return ((← get).messages.toArray.extract n).filter (·.severity == .error)

def firstError (errors : Array Message) : CommandElabM (Option String) := do
  let some msg := errors[0]? | return none
  let s        := (← msg.data.toString).trim
  return some (if s.length > 2000 then s.take 2000 ++ "…" else s)

/-- Elaborates `stx` once and measures it. -/
def measure (stx : Syntax) : CommandElabM (Run × Array Message) := do
  resetPeakRss
  let mem₀      ← readProcMem?
  let (cpu₀, _) ← rusage
  let t₀        ← IO.monoNanosNow
  let errors    ← elabCollectingErrors stx
  let t₁        ← IO.monoNanosNow
  let (cpu₁, lifetimePeakKb) ← rusage
  let mem₁      ← readProcMem?
  return (
    { wallNs      := t₁ - t₀
    , cpuMs       := cpu₁ - cpu₀
    , rssBeforeKb := mem₀.map (·.rssKb)
    , peakRssKb   := (mem₁.map (·.hwmKb)).getD lifetimePeakKb
    , rssAfterKb  := mem₁.map (·.rssKb)
    }, errors)

/-! ## Checks outside the measured region -/

unsafe def evalScriptUnsafe (env : Environment) (opts : Options) (n : Name) : Except String PlutusScript :=
  env.evalConst PlutusScript opts n

@[implemented_by evalScriptUnsafe]
opaque evalScript (env : Environment) (opts : Options) (n : Name) : Except String PlutusScript

unsafe def evalTermsUnsafe (env : Environment) (opts : Options) (n : Name) : Except String (List PlutusCore.UPLC.Term.Term) :=
  env.evalConst (List PlutusCore.UPLC.Term.Term) opts n

@[implemented_by evalTermsUnsafe]
opaque evalTerms (env : Environment) (opts : Options) (n : Name) : Except String (List PlutusCore.UPLC.Term.Term)

/-- The arguments a case applies its script to, when they are all known: none without a
    conversion function, or the value of a conversion function that takes no arguments. -/
def closedArgs? (conv? : Option Name) : CommandElabM (Option (List PlutusCore.UPLC.Term.Term)) := do
  let some f := conv? | return some []
  if (← getConstInfo f).type.isForall then return none
  return (evalTerms (← getEnv) (← getOptions) f).toOption

/-- `cekExecuteProgram p args fuel`. As an `IO` action that is never inlined, the call runs
    exactly where `timeNative` sequences it, between its two timer reads. -/
@[noinline] def runNative (p : Program) (args : List PlutusCore.UPLC.Term.Term) (fuel : Nat) : IO PlutusCore.UPLC.CekMachine.State :=
  pure (PlutusCore.UPLC.CekMachine.cekExecuteProgram p args fuel)

/-- One timed run of `cekExecuteProgram p args fuel`: its time in ns and the state it ends in. -/
def timeNativeOnce (p : Program) (args : List PlutusCore.UPLC.Term.Term) (fuel : Nat) : IO (Nat × PlutusCore.UPLC.CekMachine.State) := do
  let t₀    ← IO.monoNanosNow
  let final ← runNative p args fuel
  return ((← IO.monoNanosNow) - t₀, final)

/-- Best time of `cekExecuteProgram p args fuel` in ms, over repeated runs (at least one, then
    more until 50 ms or 1000 runs have passed), the number of runs, and the state it ends in. -/
def timeNative (p : Program) (args : List PlutusCore.UPLC.Term.Term) (fuel : Nat) : IO (Float × Nat × PlutusCore.UPLC.CekMachine.State) := do
  let (t, final) ← timeNativeOnce p args fuel
  more t t 1 final
 where
  more (best total runs : Nat) (final : PlutusCore.UPLC.CekMachine.State) :
      IO (Float × Nat × PlutusCore.UPLC.CekMachine.State) := do
    if runs < 1000 ∧ total < 50_000_000 then
      let (t, final) ← timeNativeOnce p args fuel
      more (min best t) (total + t) (runs + 1) final
    else
      return (best.toFloat / 1e6, runs, final)
  termination_by 1000 - runs

/-- Iterates `step` the way `runSteps` does, to count the steps, which `cekExecuteProgram` does not
    report. -/
def countSteps (σ : PlutusCore.UPLC.CekMachine.State) (n fuel : Nat) : Nat × String :=
  match σ with
  | .Halt _ => (n, "halt")
  | .Error  => (n, "error")
  | _       => if n < fuel then countSteps (step default σ) (n + 1) fuel else (n, "exhausted")
termination_by fuel - n

/-- How a closed script runs natively. -/
structure NativeRun where
  /-- How `cekExecuteProgram` ends: `halt`, `error`, or `exhausted` when its error is running
      out of fuel. -/
  result : String
  /-- The steps `countSteps` counts, when it ends the way `cekExecuteProgram` does. -/
  steps? : Option Nat
  /-- Best time of `cekExecuteProgram`. -/
  bestMs : Float
  runs   : Nat

def nativeRun? (script : Name) (args : List PlutusCore.UPLC.Term.Term) (fuel : Nat) : CommandElabM (Option NativeRun) := do
  let .ok ps                := evalScript (← getEnv) (← getOptions) script | return none
  let (bestMs, runs, final) ← timeNative ps.script args fuel
  let .Program _ body       := ps.script
  let (steps, counted)      := countSteps (initialState (applyParams body args)) 0 fuel
  let result                :=
    match final with
    | .Halt _ => "halt"
    -- `cekExecuteProgram` also ends in `Error` when it runs out of fuel.
    | .Error => if counted == "exhausted" then "exhausted" else "error"
    | _ => "running"
  return some
    { result
    , steps? := if counted == result then some steps else none
    , bestMs
    , runs
    }

/-- The optimized term after `#prep_uplc` succeeded. -/
structure PropInfo where
  /-- Head of the term, under its binders. -/
  head : String
  /-- Distinct objects in the term. -/
  objs : Nat
  /-- `Expr.hash` of the term, in hex: any change of the term changes it (barring collisions). -/
  hash : String

def propInfo? : CommandElabM (Option PropInfo) := do
  let some (.defnInfo info) := (← getEnv).find? (resultName ++ `prop) | return none
  let head := match stripLams info.value |>.getAppFn with
    | .const n _ => (n.replacePrefix `PlutusCore.UPLC.CekMachine .anonymous).toString
    | e          => e.ctorName
  let digits := Nat.toDigits 16 info.value.hash.toNat
  return some { head, objs := ← info.value.numObjs, hash := String.mk (List.replicate (8 - digits.length) '0' ++ digits) }
where
  stripLams : Expr → Expr
    | .lam _ _ b _ => stripLams b
    | e => e

/-- A duration in ms: in µs below 1 ms. -/
def fmtDuration (ms : Float) : String :=
  if ms < 1 then s!"{fmtMs (ms * 1000)} µs" else s!"{fmtMs ms} ms"

/-! ## Benchmark driver -/

structure Case where
  id       : String
  /-- Describes where the script comes from (reported as is). -/
  source   : Json
  /-- The `PlutusScript` constant given to `#prep_uplc`. -/
  script?  : Option Name
  conv?    : Option Name
  maxSteps : Nat

def emit (c : Case) (status : String) (error? : Option String) (runs : Array Run := #[])
    (native? : Option NativeRun := none) (prop? : Option PropInfo := none) :
    CommandElabM Unit := do
  let byTime      := runs.qsort (·.wallNs < ·.wallNs)
  let wallMin?    := byTime[0]?.map (·.wallMs)
  let wallMedian? := byTime[byTime.size / 2]?.map (·.wallMs)
  let peakDelta?  := (runs.filterMap (·.peakDeltaKb?)).toList.max?
  let j := Json.mkObj
    [ ("id"            , toJson c.id)
    , ("status"        , toJson status)
    , ("error"         , toJson error?)
    , ("source"        , c.source)
    , ("inputs"        , toJson ((c.conv?.map toString).getD "none"))
    , ("max_steps"     , toJson c.maxSteps)
    , ("runs"          , toJson (runs.map (·.report)))
    , ("wall_ms"       , toJson wallMin?)
    , ("wall_ms_median", toJson wallMedian?)
    , ("cpu_ms"        , toJson (byTime[0]?.map (·.cpuMs)))
    , ("rss_before_kb" , toJson (runs[0]?.bind (·.rssBeforeKb)))
    , ("peak_rss_kb"   , toJson (runs.map (·.peakRssKb)).toList.max?)
    , ("peak_delta_kb" , toJson peakDelta?)
    , ("rss_after_kb"  , toJson (runs.back?.bind (·.rssAfterKb)))
    , ("native_result" , toJson (native?.map (·.result)))
    , ("cek_steps"     , toJson (native?.bind (·.steps?)))
    , ("native_ms"     , toJson (native?.map (·.bestMs)))
    , ("native_runs"   , toJson (native?.map (·.runs)))
    , ("prop_head"     , toJson (prop?.map (·.head)))
    , ("prop_objs"     , toJson (prop?.map (·.objs)))
    , ("prop_hash"     , toJson (prop?.map (·.hash)))
    , ("lean_version"  , toJson Lean.versionString)
    ]
  if let some path ← IO.getEnv "PREP_UPLC_BENCH_OUT" then
    IO.FS.withFile path .append (·.putStrLn j.compress)
  let time := match wallMin? with
    | some ms => s!", {fmtMs ms} ms" ++ (if runs.size > 1 then s!" (best of {runs.size})" else "")
    | none    => ""
  let mem := match peakDelta? with
    | some kb => s!", peak +{kb / 1024} MB"
    | none    => ""
  let native := match native? with
    | some n =>
      let steps := match n.steps? with
        | some k => s!", {k} CEK steps"
        | none   => ""
      s!", native {fmtDuration n.bestMs} ({n.result}{steps})"
    | none => ""
  let prop := match prop? with
    | some p => s!", prop {p.head} ({p.objs} objects, hash {p.hash})"
    | none   => ""
  let error := match error? with
    | some e => s!": {e}"
    | none   => ""
  logInfo m!"#prep_uplc benchmark '{c.id}': {status}{time}{mem}{native}{prop}{error}"

/-- Elaborates the `#prep_uplc` command `prepStx` `n` times, each time on a fresh copy of the
    environment, stopping at the first error. Returns the runs, and that error or the optimized
    term of the last run. -/
def measureRuns (prepStx : Syntax) :
    (n : Nat) → (runs : Array Run := #[]) → CommandElabM (Array Run × Except String (Option PropInfo))
  | 0    , runs => return (runs, .ok none)
  | n + 1, runs => do
    let (run, errors, prop?) ← withoutModifyingEnv do
      let (run, errors) ← measure prepStx
      return (run, errors, ← propInfo?)
    let runs := runs.push run
    match ← firstError errors with
    | some e => return (runs, .error e)
    | none   => if n == 0 then return (runs, .ok prop?) else measureRuns prepStx n runs

/-- Measures `#prep_uplc` on `c.script?` (which must be set). -/
def benchCase (c : Case) : CommandElabM Unit := do
  let some script := c.script? | throwError "no script to benchmark"
  let native?     ←
    match ← closedArgs? c.conv? with
    | some args => nativeRun? script args c.maxSteps
    | none      => pure none
  let conv        :=
    match c.conv? with
    | some f => s!" {f}"
    | none   => ""
  let prepStx ← parseCommand s!"#prep_uplc {resultName} {script}{conv} {c.maxSteps}"
  match ← measureRuns prepStx (max 1 (bench.prepUplc.runs.get (← getOptions))) with
  | (runs, .error e)  => emit c "prep_error" e runs native?
  | (runs, .ok prop?) => emit c "ok" none runs native? prop?

/-- Resolves an optional conversion function to its full name. -/
def resolveConv? (stx : Syntax) : CommandElabM (Option Name) :=
  stx.getOptional?.mapM resolveGlobalConstNoOverload

syntax (name := benchPrepUplc) "#bench_prep_uplc " str ident (ident)? num : command

@[command_elab benchPrepUplc]
def elabBenchPrepUplc : CommandElab := (λ stx => withBenchOptions do
  let some id       := stx[1].isStrLit? | throwUnsupportedSyntax
  let const         ← resolveGlobalConstNoOverload stx[2]
  let conv?         ← resolveConv? stx[3]
  let some maxSteps := stx[4].isNatLit? | throwUnsupportedSyntax
  let script        ←
    match (← getConstInfo const).type with
    | .const ``PlutusScript _ => pure const
    | .const ``Program _ =>
      -- `#prep_uplc` wants a `PlutusScript`; the ledger language plays no part in it.
      liftCoreM <| addAndCompile <| .defnDecl {
        name := scriptName, levelParams := [], type := mkConst ``PlutusScript,
        value := mkApp2 (mkConst ``PlutusScript.mk) (mkConst ``PlutusLanguage.PlutusV3) (mkConst const),
        hints := .abbrev, safety := .safe }
      pure scriptName
    | t => throwErrorAt stx[2] m!"expected a `PlutusScript` or a `Program`, got {t}"
  benchCase
    { id
    , source  := Json.mkObj [("kind", "const"), ("name", toJson (toString const))]
    , script? := script
    , conv?
    , maxSteps
    }
 )

syntax (name := benchPrepUplcFile) "#bench_prep_uplc_file " str ident ident str (ident)? num : command

@[command_elab benchPrepUplcFile]
def elabBenchPrepUplcFile : CommandElab := (λ stx => withBenchOptions do
  let some id       := stx[1].isStrLit? | throwUnsupportedSyntax
  let lang          := stx[2].getId
  let format        := stx[3].getId
  let some path     := stx[4].isStrLit? | throwUnsupportedSyntax
  let conv?         ← resolveConv? stx[5]
  let some maxSteps := stx[6].isNatLit? | throwUnsupportedSyntax
  let source := Json.mkObj
    [ ("kind"  , "file")
    , ("path"  , toJson path)
    , ("lang"  , toJson (toString lang))
    , ("format", toJson (toString format))
    ]
  let c : Case := { id, source, script? := scriptName, conv?, maxSteps }
  -- Importing is not measured.
  let format? ← if format != `auto then pure (some format) else
    try
      pure (PlutusCore.UPLC.ScriptEncoding.Internal.importUplcImp.findWorkingFormat
        (← IO.FS.readFile path))
    catch _ => pure none
  let some format := format? | return ← emit c "import_error" s!"cannot decode '{path}' in any format"
  let errors      ← elabCollectingErrors (← parseCommand s!"#import_uplc {scriptName} {lang} {format} {path.quote}")
  if let some e ← firstError errors then
    return ← emit c "import_error" e
  benchCase c
 )

end Benchmark.PrepUplc
