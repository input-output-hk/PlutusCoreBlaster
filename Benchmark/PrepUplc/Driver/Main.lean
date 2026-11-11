import Benchmark.PrepUplc.Driver.Cases
import Benchmark.PrepUplc.Driver.Report
import Benchmark.PrepUplc.Driver.Runner

/-!
# `bench_prep_uplc`: the `#prep_uplc` benchmark driver

See `usage` and `Benchmark/README.md`.
-/

namespace Benchmark.PrepUplc.Driver

open Lean (Json toJson)
open System (FilePath)

structure Options where
  suites        : List Suite := Suite.all
  filters       : Array String := #[]
  excludes      : Array String := #[]
  jobs          : Nat := 1
  timeoutS      : Nat := 600
  maxRssMb      : Nat := 16384
  maxSteps      : Nat := 100000
  symbolicSteps : List Nat := [2000]
  runs          : Nat := 1
  leanArgs      : Array String := #[]
  label?        : Option String := none
  out?          : Option String := none
  resume?       : Option String := none
  build         : Bool := true
  thresholdPct  : Nat := 10
  minMs         : Nat := 20
  minNativeUs   : Nat := 100
  compareOut?   : Option String := none
  positional    : Array String := #[]

def Options.describe (o : Options) : Json :=
  Json.mkObj [
    ("suites"        , toJson (o.suites.map (·.name))),
    ("filters"       , toJson o.filters),
    ("excludes"      , toJson o.excludes),
    ("jobs"          , toJson o.jobs),
    ("timeout_s"     , toJson o.timeoutS),
    ("max_rss_mb"    , toJson o.maxRssMb),
    ("max_steps"     , toJson o.maxSteps),
    ("symbolic_steps", toJson o.symbolicSteps),
    ("runs"          , toJson o.runs),
    ("lean_args"     , toJson o.leanArgs),
    ("label"         , toJson o.label?)
  ]

def usage : String :=
"Usage: lake exe bench_prep_uplc <command> [options]

Benchmarks the `#prep_uplc` command on the scripts of the repository (see Benchmark/README.md).

Commands:
  list                    Print the ids of the selected cases.
  run                     Generate the case files, run them and report the results.
  report <run-dir>        Rewrite results.csv and summary.md of a run.
  compare <base> <new>    Compare two runs (run directories or results.jsonl files).

Selecting cases (list, run):
  --suite S[,S...]        all (default), conformance, repo, symbolic.
  --filter TEXT           Keep cases whose id contains TEXT (repeatable: any of them).
  --exclude TEXT          Drop cases whose id contains TEXT (repeatable).
  --max-steps N           Step budget of the conformance and repo cases (default 100000).
  --symbolic-steps N,...  Step budgets of the symbolic cases (default 2000).

Running (run):
  -j, --jobs N            Cases run in parallel (default 1; more is faster but noisier).
  --timeout S             Stop a case after S seconds (default 600).
  --max-rss-mb N          Stop a case above N MB resident (default 16384; 0: no limit).
  --runs N                Run `#prep_uplc` N times per case; report the best (default 1).
  --lean-arg ARG          Pass ARG to lean (repeatable), e.g. --lean-arg=--tstack=200000.
  --label L               Suffix of the run directory name.
  --out DIR               Run directory (default Benchmark/results/<time>-<commit>[-<label>]).
  --resume DIR            Continue an interrupted run: skip the cases it finished, rerun
                          the ones that crashed.
  --no-build              Skip `lake build Benchmark`.

Comparing (compare):
  --threshold PCT         List cases slower or faster by more than PCT% (default 10).
  --min-ms MS             Ignore cases faster than MS ms in both runs (default 20).
  --min-native-us US      Ignore native runs faster than US µs in both runs (default 100).
  --out FILE              Also write the comparison to FILE.
"

def parseNat (opt v : String) : Except String Nat :=
  match v.toNat? with
  | some n => .ok n
  | none   => .error s!"{opt} expects a number, got '{v}'"

def parseOptions (o : Options) : List String → Except String Options
  | [] => .ok o
  | "--suite" :: v :: rest => do
      let suites ← (v.splitOn ",").mapM (λ s =>
        if s == "all" then .ok Suite.all
        else match Suite.ofString? s with
          | some suite => .ok [suite]
          | none => .error s!"unknown suite '{s}'")
      parseOptions { o with suites := Suite.all.filter suites.flatten.contains } rest
  | "--filter"         :: v :: rest => parseOptions { o with filters := o.filters.push v } rest
  | "--exclude"        :: v :: rest => parseOptions { o with excludes := o.excludes.push v } rest
  | "--max-steps"      :: v :: rest => do parseOptions { o with maxSteps := ← parseNat "--max-steps" v } rest
  | "--symbolic-steps" :: v :: rest => do
      parseOptions { o with symbolicSteps := ← (v.splitOn ",").mapM (parseNat "--symbolic-steps") } rest
  | "-j"               :: v :: rest | "--jobs" :: v :: rest => do parseOptions { o with jobs := ← parseNat "--jobs" v } rest
  | "--timeout"        :: v :: rest => do parseOptions { o with timeoutS := ← parseNat "--timeout" v } rest
  | "--max-rss-mb"     :: v :: rest => do parseOptions { o with maxRssMb := ← parseNat "--max-rss-mb" v } rest
  | "--runs"           :: v :: rest => do parseOptions { o with runs := max 1 (← parseNat "--runs" v) } rest
  | "--lean-arg"       :: v :: rest => parseOptions { o with leanArgs := o.leanArgs.push v } rest
  | "--label"          :: v :: rest => parseOptions { o with label? := some v } rest
  | "--out"            :: v :: rest => parseOptions { o with out? := some v, compareOut? := some v } rest
  | "--resume"         :: v :: rest => parseOptions { o with resume? := some v } rest
  | "--no-build"            :: rest => parseOptions { o with build := false } rest
  | "--threshold"      :: v :: rest => do parseOptions { o with thresholdPct := ← parseNat "--threshold" v } rest
  | "--min-ms"         :: v :: rest => do parseOptions { o with minMs := ← parseNat "--min-ms" v } rest
  | "--min-native-us"  :: v :: rest => do
      parseOptions { o with minNativeUs := ← parseNat "--min-native-us" v } rest
  | arg                     :: rest =>
      if arg.startsWith "--lean-arg=" then
        parseOptions { o with leanArgs := o.leanArgs.push (arg.drop "--lean-arg=".length) } rest
      else if arg.startsWith "-" then .error s!"unknown option '{arg}'"
      else parseOptions { o with positional := o.positional.push arg } rest

def checkRepositoryRoot : IO Unit := do
  unless (← FilePath.pathExists "lakefile.lean") && (← FilePath.pathExists "Benchmark/PrepUplc/Harness.lean") do
    throw <| IO.userError "run bench_prep_uplc from the repository root"

/-- The cases of the repo suite, warning about script files that `repoScripts` misses. -/
def repoSuite (maxSteps : Nat) : IO (Array BenchCase) := do
  let unlisted ← unlistedScriptFiles
  unlisted.forM (λ file =>
    IO.eprintln s!"warning: {file} is not listed in `repoScripts` \
      (Benchmark/PrepUplc/Driver/Cases.lean); benchmarking it with format `auto`")
  return repoCases maxSteps unlisted

def selectCases (o : Options) : IO (Array BenchCase) := do
  let suite (s : Suite) (cases : IO (Array BenchCase)) := if o.suites.contains s then cases else pure #[]
  let conformance ← suite .conformance (conformanceCases o.maxSteps)
  let repo ← suite .repo (repoSuite o.maxSteps)
  let symbolic ← suite .symbolic (pure (symbolicCases o.symbolicSteps))
  let keep (c : BenchCase) :=
    (o.filters.isEmpty || o.filters.any (containsStr c.id ·)) && !o.excludes.any (containsStr c.id ·)
  return disambiguate ((conformance ++ repo ++ symbolic).filter keep)

def defaultRunDir (label? : Option String) : IO FilePath := do
  let time := (← tryCmd "date" #["-u", "+%Y%m%d-%H%M%S"]).getD "run"
  let rev := (← tryCmd "git" #["rev-parse", "--short=8", "HEAD"]).getD "unknown"
  let label := match label? with
    | some l => "-" ++ l
    | none   => ""
  return "Benchmark" / "results" / s!"{time}-{rev}{label}"

def readMeta (runDir : FilePath) : IO Json := do
  try IO.ofExcept (Json.parse (← IO.FS.readFile (runDir / "meta.json"))) catch _ => return Json.mkObj []

/-- Writes the result files of a run and prints its summary. -/
def finish (runDir : FilePath) (results : Array Result) : IO Unit := do
  saveResults (runDir / "results.jsonl") results
  writeCsv (runDir / "results.csv") results
  let summary := summaryMarkdown (runDir.fileName.getD runDir.toString) (← readMeta runDir) results
  IO.FS.writeFile (runDir / "summary.md") summary
  IO.println ("\n" ++ consoleSummary results)
  IO.println s!"\nFull report: {runDir / "summary.md"}; per-case data: {runDir / "results.csv"}"

def runCommand (o : Options) : IO UInt32 := do
  checkRepositoryRoot
  let cases ← selectCases o
  if cases.isEmpty then
    IO.eprintln "no cases selected"
    return 1
  let runDir ← match o.resume?, o.out? with
    | some dir, _ | none, some dir => pure (FilePath.mk dir)
    | none, none => defaultRunDir o.label?
  let resultsFile := runDir / "results.jsonl"
  if o.resume?.isNone && (← resultsFile.pathExists) then
    throw <| IO.userError s!"{runDir} already holds results; pass --resume {runDir} to continue it"
  ["raw", "logs", "setup"].forM (IO.FS.createDirAll <| runDir / ·)
  let previous ← loadResults resultsFile
  -- Cases that crashed or reported nothing (e.g. `lean` could not start) run again.
  let finished : Std.HashSet String := previous.foldl (init := {}) (λ done r =>
    if r.status == "crash" || r.status == "no_result" then done else done.insert r.id)
  let todo := cases.filter (!finished.contains ·.id)
  writeCaseFiles cases o.runs
  if o.build then
    buildBenchmark
  let setups ← moduleSetups todo
  unless ← (runDir / "meta.json").pathExists do
    IO.FS.writeFile (runDir / "meta.json") (← collectMeta o.describe).pretty
  IO.println s!"Running {todo.size} cases in {runDir} ({o.jobs} at a time)"
  let cfg : RunConfig := {
    jobs := o.jobs, timeoutS := o.timeoutS, maxRssMb := o.maxRssMb, leanArgs := o.leanArgs, runDir }
  let new ← runCases cfg todo setups (λ r n => do
    IO.FS.withFile resultsFile .append (·.putStrLn (toJson r).compress)
    let time := match r.wallMs with
      | some ms => s!" {fmt1 ms} ms"
      | none => ""
    IO.println s!"[{n}/{todo.size}] {r.status} {r.id}{time}")
  IO.FS.removeDirAll (runDir / "setup")
  let byId : Std.HashMap String Result := (previous ++ new).foldl (λ m r => m.insert r.id r) {}
  finish runDir (cases.filterMap (byId[·.id]?))
  return 0

/-- A run directory or a `results.jsonl` file → its results and metadata. -/
def loadRun (path : String) : IO (String × Json × Array Result) := do
  let p : FilePath := path
  if ← p.isDir then
    return (path, ← readMeta p, ← loadResults (p / "results.jsonl"))
  else
    let dir := p.parent.getD "."
    return (path, ← readMeta dir, ← loadResults p)

def main (args : List String) : IO UInt32 := do
  let (cmd, rest) := match args with
    | cmd :: rest => (cmd, rest)
    | [] => ("help", [])
  let o ← match parseOptions {} rest with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"error: {e}\n\n{usage}"
      return 2
  match cmd, o.positional.toList with
  | "list", [] =>
    checkRepositoryRoot
    (← selectCases o).forM (IO.println ·.id)
    return 0
  | "run", [] => runCommand o
  | "report", [dir] =>
    let (_, _, results) ← loadRun dir
    finish dir results
    return 0
  | "compare", [basePath, newPath] =>
    let (baseName, baseMeta, base) ← loadRun basePath
    let (newName, newMeta, new) ← loadRun newPath
    let report := compareMarkdown baseName newName baseMeta newMeta base new
      o.thresholdPct.toFloat o.minMs.toFloat (o.minNativeUs.toFloat / 1000)
    IO.println report
    if let some file := o.compareOut? then
      IO.FS.writeFile file report
    return 0
  | "help", _ | "--help", _ | "-h", _ =>
    IO.println usage
    return 0
  | _, _ =>
    IO.eprintln usage
    return 2

end Benchmark.PrepUplc.Driver

def main (args : List String) : IO UInt32 := do
  try Benchmark.PrepUplc.Driver.main args
  catch e =>
    IO.eprintln s!"error: {e}"
    return (1 : UInt32)
