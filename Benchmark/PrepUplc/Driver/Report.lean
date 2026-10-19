import Lean.Data.Json
import Benchmark.PrepUplc.Driver.Cases

/-!
# Benchmark results

A `Result` combines what the harness measured inside `lean` with what the driver observed from
outside (process time, exit code, timeouts). This module writes the results of a run
(`results.jsonl`, `results.csv`, `summary.md`) and compares two runs.
-/

namespace Benchmark.PrepUplc.Driver

open Lean (Json ToJson FromJson toJson)
open System (FilePath)

structure Result where
  id               : String
  suite            : String
  category         : String
  expected         : String := ""
  /-- `ok`, `import_error` or `prep_error` (from the harness), else `timeout`, `mem_limit`,
      `crash` (the process failed before reporting) or `no_result`. -/
  status           : String
  error            : Option String := none
  inputs           : String := "none"
  maxSteps         : Nat := 0
  /-- Best wall time of `#prep_uplc` over the runs. -/
  wallMs           : Option Float := none
  wallMsMedian     : Option Float := none
  cpuMs            : Option Nat := none
  rssBeforeKb      : Option Nat := none
  peakRssKb        : Option Nat := none
  /-- Largest increase of the resident set size during a run. -/
  peakDeltaKb      : Option Nat := none
  rssAfterKb       : Option Nat := none
  /-- How the native `cekExecuteProgram` run of a closed program ends: `halt`, `error` or
      `exhausted` (out of fuel). -/
  nativeResult     : Option String := none
  /-- Machine steps of that run. -/
  cekSteps         : Option Nat := none
  /-- Best time of that run. -/
  nativeMs         : Option Float := none
  nativeRuns       : Option Nat := none
  propHead         : Option String := none
  propObjs         : Option Nat := none
  /-- Hash of the optimized term. -/
  propHash         : Option String := none
  /-- The individual runs, as reported by the harness. -/
  runs             : Json := Json.arr #[]
  /-- Wall time of the whole `lean` process. -/
  processS         : Float := 0
  exitCode         : Option Nat := none
  maxRssObservedKb : Option Nat := none
  caseFile         : String := ""
  log              : String := ""
  deriving ToJson, FromJson, Inhabited

def field? (j : Json) (α : Type) [FromJson α] (key : String) : Option α :=
  (j.getObjValAs? α key).toOption

/-- Fills in what the harness reported. -/
def Result.withHarness (r : Result) (j : Json) : Result :=
  { r with
    status       := (field? j String "status"   ).getD "no_result"
    error        :=  field? j String "error"
    inputs       := (field? j String "inputs"   ).getD "none"
    maxSteps     := (field? j Nat    "max_steps").getD 0
    wallMs       :=  field? j Float  "wall_ms"
    wallMsMedian :=  field? j Float  "wall_ms_median"
    cpuMs        :=  field? j Nat    "cpu_ms"
    rssBeforeKb  :=  field? j Nat    "rss_before_kb"
    peakRssKb    :=  field? j Nat    "peak_rss_kb"
    peakDeltaKb  :=  field? j Nat    "peak_delta_kb"
    rssAfterKb   :=  field? j Nat    "rss_after_kb"
    nativeResult :=  field? j String "native_result"
    cekSteps     :=  field? j Nat    "cek_steps"
    nativeMs     :=  field? j Float  "native_ms"
    nativeRuns   :=  field? j Nat    "native_runs"
    propHead     :=  field? j String "prop_head"
    propObjs     :=  field? j Nat    "prop_objs"
    propHash     :=  field? j String "prop_hash"
    runs         := j.getObjValD     "runs" }

def statuses : List String :=
  ["ok", "import_error", "prep_error", "timeout", "mem_limit", "crash", "no_result"]

/-! ## Derived metrics -/

/-- Whether `#prep_uplc` reduced a closed program to the state the machine natively ends in. -/
def Result.fullyEvaluated (r : Result) : Bool :=
  match r.nativeResult, r.propHead with
  | some "halt"     , some head => head == "State.Halt"
  | some "error"    , some head => head == "State.Error"
  | some "exhausted", some head => head == "State.Error"
  | _               , _         => false

/-- Machine steps per second of `#prep_uplc`, on a closed program it fully evaluates (otherwise
    it did not take all of these steps). -/
def Result.prepStepsPerS? (r : Result) : Option Float := do
  guard (r.status == "ok" && r.fullyEvaluated)
  let steps ← r.cekSteps
  let ms    ← r.wallMs
  guard (ms > 0)
  return steps.toFloat * 1000 / ms

/-- Machine steps per second of the native `cekExecuteProgram` run. -/
def Result.nativeStepsPerS? (r : Result) : Option Float := do
  let steps ← r.cekSteps
  let ms    ← r.nativeMs
  guard (ms > 0)
  return steps.toFloat * 1000 / ms

/-- Programs with fewer steps are left out of the rate statistics: for them, the fixed cost of
    `#prep_uplc` (about 0.2 s) is most of the time. -/
def rateMinSteps : Nat := 1000

/-! ## Loading and saving -/

/-- One result per case: the last one given, in the order the cases first appear. -/
def latestById (results : Array Result) : Array Result :=
  let latest : Std.HashMap String Result := results.foldl (λ m r => m.insert r.id r) {}
  let ids := (results.foldl (init := (({} : Std.HashSet String), #[])) (λ (seen, ids) r =>
    if seen.contains r.id then (seen, ids) else (seen.insert r.id, ids.push r.id))).2
  ids.filterMap (latest[·]?)

/-- Reads a `results.jsonl`; for a case listed more than once, the last line wins. -/
def loadResults (file : FilePath) : IO (Array Result) := do
  if !(← file.pathExists) then return #[]
  let lines := ((← IO.FS.readFile file).splitOn "\n").filter (!·.trim.isEmpty)
  let results ← lines.toArray.mapM (λ line => IO.ofExcept (Json.parse line >>= Lean.fromJson? (α := Result)))
  return latestById results

def saveResults (file : FilePath) (results : Array Result) : IO Unit :=
  IO.FS.writeFile file <| String.join (results.toList.map (λ r => (toJson r).compress ++ "\n"))

/-! ## Formatting -/

/-- `x` with `d` decimals. -/
def fmtDec (x : Float) (d : Nat) : String :=
  let scale := 10 ^ d
  let n := (x.abs * scale.toFloat).round.toUInt64.toNat
  let frac := toString (n % scale)
  (if x < 0 then "-" else "") ++ s!"{n / scale}." ++ String.mk (List.replicate (d - frac.length) '0') ++ frac

def fmt1 (x : Float) : String := fmtDec x 1
def fmt2 (x : Float) : String := fmtDec x 2

/-- A duration in ms: in µs below 1 ms. -/
def fmtDuration (ms : Float) : String :=
  if ms < 1 then s!"{fmt1 (ms * 1000)} µs" else s!"{fmt1 ms} ms"

/-- A rate per second, with a k, M or G suffix. -/
def fmtRate (perS : Float) : String :=
  if      perS ≥ 1e9 then s!"{fmt1 (perS / 1e9)}G"
  else if perS ≥ 1e6 then s!"{fmt1 (perS / 1e6)}M"
  else if perS ≥ 1e3 then s!"{fmt1 (perS / 1e3)}k"
  else                    fmt1 perS

def fmtOpt (f : α → String) : Option α → String
  | some a => f a
  | none => "–"

def mb (kb : Nat) : Float := kb.toFloat / 1024

def sortedFloats (xs : Array Float) : Array Float := xs.qsort (· < ·)

/-- Nearest-rank percentile (`p` in [0, 1]) of sorted values. -/
def percentile (sorted : Array Float) (p : Float) : Option Float :=
  if sorted.isEmpty then none
  else sorted[((p * sorted.size.toFloat).ceil.toUInt64.toNat).max 1 - 1]?

def geomean (xs : Array Float) : Option Float :=
  if xs.isEmpty then none
  else some (Float.exp ((xs.foldl (· + ·.log) 0) / xs.size.toFloat))

def mdCell (s : String) : String :=
  (s.replace "|" "\\|").replace "\n" " "

def mdTable (header : List String) (rows : List (List String)) : String :=
  let line (cells : List String) := "| " ++ " | ".intercalate (cells.map mdCell) ++ " |"
  "\n".intercalate ([line header, line (header.map (λ _ => "---"))] ++ rows.map line) ++ "\n"

def firstLine (s : String) (max := 200) : String :=
  let l := ((s.splitOn "\n").headD "").trim
  if l.length > max then l.take max ++ "…" else l

def Result.propDescr (r : Result) : String :=
  match r.propHead, r.propObjs with
  | some h, some n => s!"{h} ({n})"
  | some h, none => h
  | _, _ => "–"

/-! ## CSV -/

def csvField (s : String) : String :=
  if s.any (λ c => c == ',' || c == '"' || c == '\n') then "\"" ++ s.replace "\"" "\"\"" ++ "\"" else s

def csvHeader : List String :=
  [ "id"
  , "suite"
  , "category"
  , "expected"
  , "inputs"
  , "max_steps"
  , "status"
  , "wall_ms"
  , "wall_ms_median"
  , "cpu_ms"
  , "rss_before_kb"
  , "peak_rss_kb"
  , "peak_delta_kb"
  , "rss_after_kb"
  , "native_result"
  , "cek_steps"
  , "native_ms"
  , "native_runs"
  , "prep_steps_per_s"
  , "native_steps_per_s"
  , "prop_head"
  , "prop_objs"
  , "prop_hash"
  , "process_s"
  , "exit_code"
  , "max_rss_observed_kb"
  , "error"
  ]

def Result.csvRow (r : Result) : List String :=
  let opt {α} [ToString α] (o : Option α) : String := (o.map toString).getD ""
  let rate (perS? : Option Float) : String       := (perS?.map (λ perS => toString perS.round.toUInt64)).getD ""
  [ r.id
  , r.suite
  , r.category
  , r.expected
  , r.inputs
  , toString r.maxSteps
  , r.status
  , (r.wallMs.map fmt2).getD ""
  , (r.wallMsMedian.map fmt2).getD ""
  , opt r.cpuMs
  , opt r.rssBeforeKb
  , opt r.peakRssKb
  , opt r.peakDeltaKb
  , opt r.rssAfterKb
  , opt r.nativeResult
  , opt r.cekSteps
  , (r.nativeMs.map (fmtDec · 4)).getD ""
  , opt r.nativeRuns
  , rate r.prepStepsPerS?
  , rate r.nativeStepsPerS?
  , opt r.propHead
  , opt r.propObjs
  , opt r.propHash
  , fmt2 r.processS
  , opt r.exitCode
  , opt r.maxRssObservedKb
  , opt r.error
  ]

def writeCsv (file : FilePath) (results : Array Result) : IO Unit :=
  IO.FS.writeFile file <| String.join <|
    (csvHeader :: results.toList.map (·.csvRow)).map (λ row => ",".intercalate (row.map csvField) ++ "\n")

/-! ## Summary -/

def metaLine (runInfo : Json) (key : String) : String :=
  match runInfo.getObjValD key with
  | .str s => s
  | .null => "?"
  | j => j.compress

def statusTable (results : Array Result) : String :=
  let suites := Suite.all.map (·.name) |>.filter (λ s => results.any (·.suite == s))
  mdTable (["suite", "cases"] ++ statuses) <| suites.map (λ s =>
    let rs := results.filter (·.suite == s)
    [s, toString rs.size] ++ statuses.map (λ st => toString (rs.filter (·.status == st)).size))

def totalsTable (results : Array Result) : String :=
  let suites := Suite.all.map (·.name) |>.filter (λ s => results.any (·.suite == s))
  mdTable ["suite", "ok cases", "total s", "median ms", "p90 ms", "max ms", "median peak Δ MB", "max peak Δ MB"] <| suites.map (λ s =>
    let rs := results.filter (λ r => r.suite == s && r.status == "ok")
    let times := sortedFloats (rs.filterMap (·.wallMs))
    let mems := sortedFloats (rs.filterMap (·.peakDeltaKb) |>.map mb)
    [s, toString rs.size, fmt1 (times.foldl (· + ·) 0 / 1000), fmtOpt fmt1 (percentile times 0.5),
     fmtOpt fmt1 (percentile times 0.9), fmtOpt fmt1 times.back?, fmtOpt fmt1 (percentile mems 0.5),
     fmtOpt fmt1 mems.back?])

def topTable (results : Array Result) (key : Result → Option Float) (n : Nat) : String :=
  let rs := results.filter (λ r => r.status == "ok" && (key r).isSome)
    |>.qsort (λ a b => (key a).getD 0 > (key b).getD 0)
  mdTable ["id", "ms", "peak Δ MB", "CEK steps", "prop (objects)"] <| (rs.toList.take n).map (λ r =>
    [r.id, fmtOpt fmt1 r.wallMs, fmtOpt (fmt1 ∘ mb) r.peakDeltaKb, fmtOpt toString r.cekSteps, r.propDescr])

def categoryRow (category : String) (rs : Array Result) : Float × List String :=
  let times := sortedFloats (rs.filterMap Result.wallMs)
  let total := times.foldl (· + ·) 0
  let mems := sortedFloats (rs.filterMap Result.peakDeltaKb |>.map mb)
  (total, [category, toString rs.size, fmt1 total, fmtOpt fmt1 (percentile times 0.5),
    fmtOpt fmt1 times.back?, fmtOpt fmt1 mems.back?])

def categoryTable (results : Array Result) : String :=
  let groups := results.foldl (init := ({} : Std.HashMap String (Array Result))) (λ groups r =>
    if r.suite == Suite.conformance.name && r.status == "ok" then
      groups.alter r.category (λ g => some ((g.getD #[]).push r))
    else groups)
  let rows := groups.fold (init := #[]) (λ rows category rs => rows.push (categoryRow category rs))
  mdTable ["category", "cases", "total ms", "median ms", "max ms", "max peak Δ MB"]
    (rows.qsort (λ a b => a.1 > b.1) |>.toList.map (·.2))

def nativeTable (results : Array Result) : String :=
  let suites := Suite.all.map (·.name) |>.filter (λ s => results.any (λ r => r.suite == s && r.nativeMs.isSome))
  mdTable ["suite", "cases", "total", "median", "p90", "max"] <| suites.map (λ s =>
    let times := sortedFloats (results.filter (·.suite == s) |>.filterMap (·.nativeMs))
    [s, toString times.size, fmtDuration (times.foldl (· + ·) 0), fmtOpt fmtDuration (percentile times 0.5),
     fmtOpt fmtDuration (percentile times 0.9), fmtOpt fmtDuration times.back?])

def topNativeTable (results : Array Result) (n : Nat) : String :=
  let rs := results.filter (·.nativeMs.isSome) |>.qsort (λ a b => a.nativeMs.getD 0 > b.nativeMs.getD 0)
  mdTable ["id", "native", "result", "CEK steps", "`#prep_uplc` ms"] <| (rs.toList.take n).map (λ r =>
    [r.id, fmtOpt fmtDuration r.nativeMs, fmtOpt id r.nativeResult, fmtOpt toString r.cekSteps,
     fmtOpt fmt1 r.wallMs])

/-- Cases whose optimized term is not the state the program natively ends in. -/
def notFullyEvaluated (results : Array Result) : Array Result :=
  results.filter (λ r => r.status == "ok" && r.nativeResult.isSome && r.propHead.isSome && !r.fullyEvaluated)

/-- Median and best machine steps per second, per suite, over the closed programs of at least
    `rateMinSteps` steps. -/
def ratesTable (results : Array Result) : String :=
  let rated  := results.filter (λ r => r.cekSteps.getD 0 ≥ rateMinSteps)
  let suites := Suite.all.map (·.name) |>.filter (λ s => rated.any (·.suite == s))
  mdTable ["suite", "cases", "`#prep_uplc` median", "`#prep_uplc` best", "native median", "native best"] <| suites.map (λ s =>
    let rs     := rated.filter (·.suite == s)
    let prep   := sortedFloats (rs.filterMap (·.prepStepsPerS?))
    let native := sortedFloats (rs.filterMap (·.nativeStepsPerS?))
    [s, toString rs.size, fmtOpt fmtRate (percentile prep 0.5), fmtOpt fmtRate prep.back?,
     fmtOpt fmtRate (percentile native 0.5), fmtOpt fmtRate native.back?])

/-- The `n` closed programs that take the most machine steps, with their rates. -/
def topStepsTable (results : Array Result) (n : Nat) : String :=
  let rs := results.filter (·.cekSteps.isSome) |>.qsort (λ a b => a.cekSteps.getD 0 > b.cekSteps.getD 0)
  mdTable ["id", "CEK steps", "`#prep_uplc` ms", "`#prep_uplc` steps/s", "native", "native steps/s"] <| (rs.toList.take n).map (λ r =>
    [r.id, fmtOpt toString r.cekSteps, fmtOpt fmt1 r.wallMs, fmtOpt fmtRate r.prepStepsPerS?,
     fmtOpt fmtDuration r.nativeMs, fmtOpt fmtRate r.nativeStepsPerS?])

/-- What the rates mean, above their tables. -/
def ratesExplanation : String :=
  s!"The machine steps a closed program takes, per second of `#prep_uplc` (for the programs it fully \
    evaluates) or of the native run. Programs of fewer than {rateMinSteps} steps are left out of the \
    statistics: for them, the fixed cost of `#prep_uplc` (about 0.2 s) is most of the time.\n\n"

/-- A section of a Markdown report. -/
def mdSection (title body : String) : String :=
  s!"## {title}\n\n{body}\n"

def summaryMarkdown (runName : String) (runInfo : Json) (results : Array Result) : String :=
  let info := metaLine runInfo
  let header := s!"# `#prep_uplc` benchmark: {runName}\n\n\
    - Started {info "started_utc"} on {info "host"} ({info "cpu"}, {info "cores"} cores, \
      {info "mem_total"}), {info "os"}\n\
    - {info "lean"}\n\
    - PlutusCore {info "plutuscore"}; Blaster {info "blaster"}; conformance tests of plutus \
      {info "conformance"}\n\
    - Options: {info "options"}\n\n"
  let partial_ := notFullyEvaluated results
  let failures := results.filter (·.status != "ok")
  let failureLine (r : Result) := s!"- `{r.id}`: **{r.status}**: {mdCell (firstLine (r.error.getD ""))} \
    (rerun: `lake lean {r.caseFile}`; log: `{r.log}`)\n"
  let sections : List (Option String) := [
    some (mdSection "Status" (statusTable results)),
    some (mdSection "Time and memory of `#prep_uplc` (ok cases)" (totalsTable results)),
    if results.any (·.cekSteps.isSome) then
      some (mdSection "Machine steps per second" <|
        ratesExplanation ++ ratesTable results ++ "\n" ++ topStepsTable results 10)
    else none,
    some (mdSection "Slowest" (topTable results (·.wallMs) 20)),
    some (mdSection "Most memory" (topTable results (λ r => r.peakDeltaKb.map mb) 20)),
    if results.any (·.suite == Suite.conformance.name) then
      some (mdSection "Conformance by category" (categoryTable results))
    else none,
    if results.any (·.nativeMs.isSome) then
      some (mdSection "Native `cekExecuteProgram` (closed programs)" <|
        "Best time of the compiled machine running each program, whatever `#prep_uplc` did.\n\n" ++
          nativeTable results ++ "\n" ++ topNativeTable results 10)
    else none,
    if partial_.isEmpty then none
    else some (mdSection s!"Not fully evaluated ({partial_.size})" <|
      "Closed programs whose optimized term is not the state the program natively ends in.\n\n" ++
        mdTable ["id", "native", "CEK steps", "prop (objects)"]
          (partial_.toList.map (λ r => [r.id, fmtOpt id r.nativeResult, fmtOpt toString r.cekSteps, r.propDescr]))),
    if failures.isEmpty then none
    else some (mdSection s!"Failures ({failures.size})" (String.join (failures.toList.map failureLine)))]
  header ++ String.join (sections.filterMap id)

/-- The part of the summary printed on the console. -/
def consoleSummary (results : Array Result) : String :=
  let rates := if results.any (·.cekSteps.isSome) then s!"\nMachine steps per second (closed programs of at least {rateMinSteps} steps)\n\n{ratesTable results}" else ""
  "Status\n\n" ++ statusTable results ++ "\nTime and memory of `#prep_uplc` (ok cases)\n\n" ++
    totalsTable results ++ rates ++ "\nSlowest\n\n" ++ topTable results (·.wallMs) 10

/-! ## Comparing two runs -/

/-- `(new / base, base, new)` for the pairs where `key` (a duration in ms) is known in both runs
    and at least `floor` in one of them. -/
def ratios (pairs : Array (Result × Result)) (key : Result → Option Float) (floor : Float) :
    Array (Float × Result × Result) :=
  pairs.filterMap (λ (b, n) => do
    let tb ← key b
    let tn ← key n
    guard (tb > 0 && max tb tn ≥ floor)
    pure (tn / tb, b, n))

/-- The ratios above `1 + threshold%`, slowest first, and those below its inverse, fastest first. -/
def slowerFaster (rs : Array (Float × Result × Result)) (threshold : Float) :
    Array (Float × Result × Result) × Array (Float × Result × Result) :=
  (rs.filter (·.1 > 1 + threshold / 100) |>.qsort (λ a b => a.1 > b.1),
   rs.filter (·.1 < 1 / (1 + threshold / 100)) |>.qsort (λ a b => a.1 < b.1))

def Result.nativeDescr (r : Result) : String :=
  match r.nativeResult, r.cekSteps with
  | some res, some n => s!"{res}, {n} steps"
  | some res, none => res
  | none, _ => "–"

/-- Whether the optimized term differs; by hash when both runs have one. -/
def propChanged (b n : Result) : Bool :=
  match b.propHash, n.propHash with
  | some hb, some hn => hb != hn
  | _, _ => b.propHead != n.propHead || b.propObjs != n.propObjs

def compareMarkdown (baseName newName : String) (baseMeta newMeta : Json) (base new : Array Result) (threshold minMs minNativeMs : Float) : String :=
  let baseById : Std.HashMap String Result := base.foldl (λ m r => m.insert r.id r) {}
  let newById : Std.HashMap String Result := new.foldl (λ m r => m.insert r.id r) {}
  let pairs := new.filterMap (λ n => (baseById[n.id]?).map (·, n))
  let both := pairs.filter (λ (b, n) => b.status == "ok" && n.status == "ok")
  let native := pairs.filter (λ (b, n) => b.nativeMs.isSome && n.nativeMs.isSome)
  let suitesOf (ps : Array (Result × Result)) :=
    Suite.all.map (·.name) |>.filter (λ st => ps.any (·.2.suite == st))
  let geo (ps : Array (Result × Result)) (key : Result → Option Float) :=
    fmtOpt fmt2 (geomean ((ratios ps key 0).map (·.1)))
  let total (ps : Array (Result × Result)) (side : Result × Result → Result) (key : Result → Option Float) :=
    ps.foldl (λ acc p => acc + ((key (side p)).getD 0)) 0
  let prepSummary := mdTable ["suite", "cases", "base total s", "new total s", "geomean time ratio",
      "geomean peak Δ ratio", "geomean steps/s ratio"] ((suitesOf both).map (λ st =>
    let ps := both.filter (·.2.suite == st)
    [st, toString ps.size, fmt1 (total ps (·.1) (·.wallMs) / 1000), fmt1 (total ps (·.2) (·.wallMs) / 1000),
     geo ps (·.wallMs), geo ps (λ r => r.peakDeltaKb.map (·.toFloat)), geo ps (·.prepStepsPerS?)]))
  let nativeSummary := mdTable ["suite", "cases", "base total", "new total", "geomean time ratio", "geomean steps/s ratio"]
    ((suitesOf native).map (λ st =>
      let ps := native.filter (·.2.suite == st)
      [st, toString ps.size, fmtDuration (total ps (·.1) (·.nativeMs)),
       fmtDuration (total ps (·.2) (·.nativeMs)), geo ps (·.nativeMs), geo ps (·.nativeStepsPerS?)]))
  let prepTable (rs : Array (Float × Result × Result)) :=
    mdTable ["id", "base ms", "new ms", "ratio", "base peak Δ MB", "new peak Δ MB"] <|
      rs.toList.take 40 |>.map (λ (ratio, b, n) =>
        [n.id, fmt1 (b.wallMs.getD 0), fmt1 (n.wallMs.getD 0), fmt2 ratio,
         fmtOpt (fmt1 ∘ mb) b.peakDeltaKb, fmtOpt (fmt1 ∘ mb) n.peakDeltaKb])
  let nativeTable (rs : Array (Float × Result × Result)) :=
    mdTable ["id", "base", "new", "ratio"] <| rs.toList.take 40 |>.map (λ (ratio, b, n) =>
      [n.id, fmtOpt fmtDuration b.nativeMs, fmtOpt fmtDuration n.nativeMs, fmt2 ratio])
  let prepRatios                   := ratios both (·.wallMs) minMs
  let nativeRatios                 := ratios native (·.nativeMs) minNativeMs
  let (slower, faster)             := slowerFaster prepRatios threshold
  let (nativeSlower, nativeFaster) := slowerFaster nativeRatios threshold
  let statusChanges := pairs.filter (λ (b, n) => b.status != n.status)
  let onlyBase := base.filter (!newById.contains ·.id)
  let onlyNew := new.filter (!baseById.contains ·.id)
  let examples (rs : Array Result) :=
    if rs.isEmpty then "" else
      ": " ++ ", ".intercalate (rs.toList.take 10 |>.map (s!"`{·.id}`")) ++ (if rs.size > 10 then ", …" else "")
  let nativeChanges := pairs.filter (λ (b, n) =>
    b.nativeResult.isSome && n.nativeResult.isSome &&
      (b.nativeResult != n.nativeResult || b.cekSteps != n.cekSteps))
  let outputChanges := both.filter (λ (b, n) => propChanged b n)
  let prepLimits (count : Nat)   := s!"{fmt1 threshold}% ({count} of {prepRatios.size} cases of at least {fmt1 minMs} ms)"
  let nativeLimits (count : Nat) := s!"{fmt1 threshold}% ({count} of {nativeRatios.size} runs of at least {fmtDuration minNativeMs})"
  let header := s!"# `#prep_uplc` benchmark comparison\n\n\
    - Base: {baseName} (Blaster {metaLine baseMeta "blaster"}; PlutusCore {metaLine baseMeta "plutuscore"})\n\
    - New: {newName} (Blaster {metaLine newMeta "blaster"}; PlutusCore {metaLine newMeta "plutuscore"})\n\
    - Ratios are new / base: above 1 is slower or bigger, except for steps per second, where above 1 is faster.\n\
    - The geometric means are the overall comparison. The lists of slower and faster cases show single cases, \
      which vary from run to run: a few land there even when nothing changed.\n\n"
  let sections : List (Option String) := [
    some (mdSection "`#prep_uplc`, cases ok in both runs" prepSummary),
    if native.isEmpty then none
    else some (mdSection "Native `cekExecuteProgram`, closed programs run in both" nativeSummary),
    some (mdSection s!"Cases where `#prep_uplc` is slower by more than {prepLimits slower.size}" (prepTable slower)),
    some (mdSection s!"Cases where `#prep_uplc` is faster by more than {prepLimits faster.size}" (prepTable faster)),
    if native.isEmpty then none
    else some (mdSection s!"Cases where the native run is slower by more than {nativeLimits nativeSlower.size}" (nativeTable nativeSlower)),
    if native.isEmpty then none
    else some (mdSection s!"Cases where the native run is faster by more than {nativeLimits nativeFaster.size}" (nativeTable nativeFaster)),
    some (mdSection s!"Status changes ({statusChanges.size})" <|
      mdTable ["id", "base", "new"] (statusChanges.toList.map (λ (b, n) => [n.id, b.status, n.status]))),
    if onlyBase.isEmpty && onlyNew.isEmpty then none
    else some (mdSection "Cases in one run only" s!"- Only in base: {onlyBase.size}{examples onlyBase}\n\
      - Only in new: {onlyNew.size}{examples onlyNew}\n"),
    some (mdSection s!"Native result or step count changed ({nativeChanges.size})" <|
      mdTable ["id", "base", "new"] (nativeChanges.toList.map (λ (b, n) => [n.id, b.nativeDescr, n.nativeDescr]))),
    some (mdSection s!"Optimized term changed ({outputChanges.size})" <|
      mdTable ["id", "base prop (objects)", "new prop (objects)"] (outputChanges.toList.map (λ (b, n) =>
        [n.id, b.propDescr ++ fmtOpt (" " ++ ·) b.propHash, n.propDescr ++ fmtOpt (" " ++ ·) n.propHash])))]
  header ++ String.join (sections.filterMap id)

end Benchmark.PrepUplc.Driver
