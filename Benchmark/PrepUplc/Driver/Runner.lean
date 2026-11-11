import Lean.Data.Json
import Std.Sync.Mutex
import Benchmark.PrepUplc.Driver.Cases
import Benchmark.PrepUplc.Driver.Report

/-!
# Running the cases

Each case runs in its own `lean` process, started with the module setup that `lake setup-file`
computes (the same setup `lake lean` would use). It loads the precompiled PlutusCore and Blaster
libraries, so `#prep_uplc` runs native code as in `lake build`, while the driver keeps the
process id to watch its memory and to stop it.
-/

namespace Benchmark.PrepUplc.Driver

open Lean (Json Name toJson)
open System (FilePath)

structure RunConfig where
  jobs : Nat
  timeoutS : Nat
  /-- 0 disables the limit. -/
  maxRssMb : Nat
  leanArgs : Array String
  runDir : FilePath

def leanCmd : IO String := return (← IO.getEnv "LEAN").getD "lean"
def lakeCmd : IO String := return (← IO.getEnv "LAKE").getD "lake"

/-- Runs a command and returns its standard output; throws if it fails. -/
def runCmd (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode != 0 then
    throw <| IO.userError s!"`{cmd} {" ".intercalate args.toList}` failed with exit code {out.exitCode}:\n{out.stderr}"
  return out.stdout

def tryCmd (cmd : String) (args : Array String) : IO (Option String) :=
  try return some (← runCmd cmd args).trim catch _ => return none

/-- Builds everything the cases import (see `Benchmark.lean`). -/
def buildBenchmark : IO Unit := do
  let child ← IO.Process.spawn { cmd := ← lakeCmd, args := #["build", "Benchmark"] }
  if (← child.wait) != 0 then
    throw <| IO.userError "`lake build Benchmark` failed"

/-- The module setup of one case file per distinct list of imports. -/
def moduleSetups (cases : Array BenchCase) : IO (Std.HashMap (Array Name) Json) :=
  cases.foldlM (init := {}) (λsetups c => do
    if setups.contains c.imports then return setups
    let out ← runCmd (← lakeCmd) #["setup-file", c.file.toString]
    return setups.insert c.imports (← IO.ofExcept (Json.parse out)))

/-- Resident set size of process `pid` in kB, or 0 when unknown (outside Linux). -/
def rssKbOf (pid : UInt32) : IO Nat := do
  let status ← try IO.FS.readFile s!"/proc/{pid}/status" catch _ => return 0
  return ((status.splitOn "\n").findSome? (λ line =>
    if line.startsWith "VmRSS:" then ((line.drop 6).trim.takeWhile Char.isDigit).toNat? else none)).getD 0

/-- The exit code of `child`, if it exits within `tries` checks 200 ms apart. -/
def exitWithin (child : IO.Process.Child stdio) : (tries : Nat) → IO (Option UInt32)
  | 0 => pure none
  | tries + 1 => do
    match ← child.tryWait with
    | some code => pure (some code)
    | none =>
      IO.sleep 200
      exitWithin child tries

/-- Stops a process with `Child.kill`, then with SIGKILL if it is still alive 10 s later. -/
def terminate (child : IO.Process.Child stdio) : IO UInt32 := do
  child.kill
  if let some code ← exitWithin child 50 then return code
  discard <| IO.Process.output { cmd := "kill", args := #["-KILL", toString child.pid] }
  child.wait

/-- How the process of a case ended. -/
structure Exit where
  code : UInt32
  /-- Why the driver stopped the process, if it did: `timeout` or `mem_limit`. -/
  stoppedBy? : Option String := none
  /-- The largest resident set size seen. -/
  maxRssKb : Nat

/-- Waits for `child` to exit, sampling its memory every 200 ms, and stops it once it runs past
    the time or memory limit of `cfg` (`start` is when it started, from `IO.monoMsNow`). -/
partial def monitor (cfg : RunConfig) (child : IO.Process.Child stdio) (start : Nat)
    (maxRssKb := 0) : IO Exit := do
  if let some code ← child.tryWait then
    return { code, maxRssKb }
  let rss      ← rssKbOf child.pid
  let maxRssKb := max maxRssKb rss
  let now      ← IO.monoMsNow
  let stop?    :=
    if now - start > cfg.timeoutS * 1000 then some "timeout"
    else if cfg.maxRssMb > 0 && rss > cfg.maxRssMb * 1024 then some "mem_limit"
    else none
  match stop? with
  | some reason => return { code := ← terminate child, stoppedBy? := some reason, maxRssKb }
  | none =>
    IO.sleep 200
    monitor cfg child start maxRssKb

def lastLines (s : String) (n : Nat) : String :=
  let lines := (s.splitOn "\n").filter (!·.trim.isEmpty)
  "\n".intercalate (lines.drop (lines.length - n))

/-- The measurement the harness appended to `file`, if it got that far. -/
def readHarness? (file : FilePath) : IO (Option Json) := do
  if !(← file.pathExists) then return none
  let lines := ((← IO.FS.readFile file).splitOn "\n").filter (!·.trim.isEmpty)
  return lines.getLast?.bind (Json.parse · |>.toOption)

def runCase (cfg : RunConfig) (setup : Json) (c : BenchCase) : IO Result := do
  -- `disambiguate` makes module names unique, even when distinct ids have the same slug.
  let name      := c.module.toString
  let setupFile := cfg.runDir / "setup" / s!"{name}.json"
  let rawFile   := cfg.runDir / "raw" / s!"{name}.jsonl"
  let logFile   := cfg.runDir / "logs" / s!"{name}.log"
  IO.FS.writeFile setupFile (setup.setObjVal! "name" (toJson c.module)).compress
  if ← rawFile.pathExists then IO.FS.removeFile rawFile
  let start ← IO.monoMsNow
  -- The shell sends the output of `lean` to the log and then becomes `lean` (same process id).
  -- Reading the output through pipes instead would leak their file descriptors: nothing closes
  -- them once the process has exited.
  let child ← IO.Process.spawn {
    cmd := "/bin/sh"
    args := #["-c", "exec \"$@\" > \"$PREP_UPLC_BENCH_LOG\" 2>&1", "sh", ← leanCmd,
      "--setup", setupFile.toString, "-DElab.async=false"] ++ cfg.leanArgs ++ #[c.file.toString]
    env := #[("PREP_UPLC_BENCH_OUT", some rawFile.toString), ("PREP_UPLC_BENCH_LOG", some logFile.toString)]
    stdin := .null, stdout := .null, stderr := .null }
  let exit      ← monitor cfg child start
  let elapsedMs := (← IO.monoMsNow) - start
  let output    ← try IO.FS.readFile logFile catch _ => pure ""
  IO.FS.removeFile setupFile
  let r : Result := {
    id := c.id, suite := c.suite.name, category := c.category, expected := c.expected,
    status := "no_result", processS := elapsedMs.toFloat / 1000, exitCode := some exit.code.toNat,
    maxRssObservedKb := if exit.maxRssKb > 0 then some exit.maxRssKb else none,
    caseFile := c.file.toString, log := logFile.toString }
  if let some j ← readHarness? rawFile then
    return r.withHarness j
  let error := match exit.stoppedBy? with
    | some "timeout" => s!"stopped after {cfg.timeoutS} s"
    | some _ => s!"stopped at {exit.maxRssKb / 1024} MB resident (limit {cfg.maxRssMb} MB)"
    | none => lastLines output 5
  return { r with status := exit.stoppedBy?.getD (if exit.code != 0 then "crash" else "no_result"), error }

/-- The work queue the workers share: the next case to start, and how many have finished. -/
abbrev Queue := Std.Mutex (Nat × Nat)

/-- Takes cases off `queue` and runs them until none is left; returns their results. -/
partial def worker (queue : Queue) (cases : Array BenchCase) (run : BenchCase → IO Result)
    (finished : Result → IO Unit) (results : Array Result := #[]) : IO (Array Result) := do
  let i ← queue.atomically (modifyGet (λ (next, done) => (next, (next + 1, done))))
  match cases[i]? with
  | none => return results
  | some c =>
    let r ← run c
    finished r
    worker queue cases run finished (results.push r)

/-- Runs `cases` on `cfg.jobs` workers; `onDone` is called (one call at a time) with each result
    and the number of cases finished so far. -/
def runCases (cfg : RunConfig) (cases : Array BenchCase) (setups : Std.HashMap (Array Name) Json)
    (onDone : Result → Nat → IO Unit) : IO (Array Result) := do
  let queue ← Std.Mutex.new (0, 0)
  let run (c : BenchCase) : IO Result :=
    try runCase cfg setups[c.imports]! c catch e =>
      pure { id := c.id, suite := c.suite.name, category := c.category, expected := c.expected,
             status := "crash", error := some (toString e), caseFile := c.file.toString }
  let finished (r : Result) : IO Unit := queue.atomically do
    let (next, done) ← get
    set (next, done + 1)
    onDone r (done + 1)
  let tasks ← (List.range (max 1 cfg.jobs)).mapM (λ _ =>
    IO.asTask (worker queue cases run finished) .dedicated)
  let results ← tasks.mapM (λ t => do IO.ofExcept (← IO.wait t))
  return results.toArray.flatten

/-! ## Run metadata -/

def readFirstField? (file : FilePath) (key : String) : IO (Option String) := do
  let content ← try IO.FS.readFile file catch _ => return none
  return (content.splitOn "\n").findSome? (λ line =>
    if line.startsWith key then some ((line.drop key.length).trim.dropWhile (· == ':') |>.trim) else none)

/-- The Blaster revision the build uses: the manifest's pin and the checked-out tree. -/
def blasterRevision : IO String := do
  let pinned ← try
      let manifest     ← IO.ofExcept (Json.parse (← IO.FS.readFile "lake-manifest.json"))
      let pkgs         ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages")
      let some blaster := pkgs.find? (field? · String "name" == some "Blaster") | pure "?"
      pure s!"{(field? blaster String "inputRev").getD "?"} @ {((field? blaster String "rev").getD "?").take 12}"
    catch _ => pure "?"
  let checkout := (← tryCmd "git" #["-C", ".lake/packages/Blaster", "describe", "--always", "--dirty", "--abbrev=12"]).getD "?"
  return s!"{pinned} (checkout {checkout})"

def gitRevision : IO String := do
  let rev   := (← tryCmd "git" #["rev-parse", "--short=12", "HEAD"]).getD "?"
  let dirty := !((← tryCmd "git" #["status", "--porcelain", "--untracked-files=no"]).getD "").isEmpty
  return rev ++ (if dirty then "-dirty" else "")

def collectMeta (options : Json) : IO Json := do
  let memKb := (← readFirstField? "/proc/meminfo" "MemTotal").bind (λ s => (s.takeWhile Char.isDigit).toNat?)
  return Json.mkObj [
    ("started_utc", toJson ((← tryCmd "date" #["-u", "+%Y-%m-%dT%H:%M:%SZ"]).getD "?")),
    ("host"       , toJson ((← tryCmd "hostname" #[]).getD "?")),
    ("os"         , toJson ((← tryCmd "uname" #["-srm"]).getD "?")),
    ("cpu"        , toJson ((← readFirstField? "/proc/cpuinfo" "model name").getD "?")),
    ("cores"      , toJson ((← tryCmd "getconf" #["_NPROCESSORS_ONLN"]).getD "?")),
    ("mem_total"  , toJson ((memKb.map (λ kb => s!"{kb / 1024 / 1024} GB")).getD "?")),
    ("lean"       , toJson ((← tryCmd (← leanCmd) #["--version"]).getD "?")),
    ("plutuscore" , toJson (← gitRevision)),
    ("blaster"    , toJson (← blasterRevision)),
    ("conformance", toJson ((← tryCmd "git" #["-C", ".plutus-conformance", "describe", "--always", "--tags", "--abbrev=12"]).getD "?")),
    ("options"    , options)]

end Benchmark.PrepUplc.Driver
