import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.FlatEncoding

/-!
Native CEK benchmark for the Plutus VM Benchmark image contract.

`check FILE [MAX_STEPS]` prints one headerless `vm,script,status,cpu,mem` CSV row.
`time FILE d3,eval MEASURE_MS [MAX_STEPS]` prints loop markers and timing CSV rows,
prefixed by `PVB_RESULT <loop> `. File I/O is outside timing. D3 converts the raw bytes,
decodes Flat, and evaluates on every iteration; eval decodes once before timing.

Both paths use the library's compiled-in variant E costs and builtin semantics (PlutusV3,
protocol version 11). Each evaluation has fresh state and counts costs, startup included.
An exhausted step limit is an infrastructure error, never a CEK evaluation error.
-/

namespace Benchmark.Cek

open PlutusCore.UPLC.Term (Program)
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.ExBudget (ExBudget)
open PlutusCore.UPLC.FlatEncoding (decodeProgramFromByteString)

def vm : String := "plutuscore-lean"
def defaultMaxSteps : Nat := 100_000_000
def timingHeader : String := "vm,script,mean_ns,median_ns,min_ns,max_ns,stddev_ns,iterations"

def csvField (s : String) : String :=
  if s.contains ',' || s.contains '"' || s.contains '\n' || s.contains '\r' then
    "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else s

def scriptName (path : System.FilePath) : String :=
  path.fileStem.getD path.toString

/-- Each raw byte is one character of the decoder's byte-string representation. UTF-8
decoding would replace or reject arbitrary Flat bytes. This conversion belongs to D3. -/
def decode (bytes : ByteArray) : Except String Program :=
  let input := String.mk (bytes.data.toList.map Char.ofUInt8)
  match decodeProgramFromByteString input with
  | some program => .ok program
  | none => .error "Flat decode failed"

structure Outcome where
  ok : Bool
  cost : ExBudget
deriving BEq

def evaluate (program : Program) (maxSteps : Nat) : Except String Outcome :=
  let (state, cost) := cekExecuteProgramWithCost .defaultFunSemanticsVariantE program [] maxSteps
  match state with
  | .Halt _ => .ok ⟨true, cost⟩
  | .Error => .ok ⟨false, cost⟩
  | _ => .error s!"CEK step limit exhausted ({maxSteps})"

/-- Non-inlined IO boundaries prevent the compiler from moving the pure evaluation out of
the repeated timed operation. The status and both cost components are consumed each time. -/
@[noinline] def runEval (program : Program) (maxSteps : Nat) : IO Outcome :=
  IO.ofExcept (evaluate program maxSteps)

@[noinline] def runD3 (bytes : ByteArray) (maxSteps : Nat) : IO Outcome :=
  IO.ofExcept (decode bytes >>= fun program => evaluate program maxSteps)

def check (path : System.FilePath) (maxSteps : Nat) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let outcome ← runD3 bytes maxSteps
  IO.println s!"{vm},{csvField (scriptName path)},{if outcome.ok then "ok" else "error"},{outcome.cost.exBudgetCPU.unExCPU},{outcome.cost.exBudgetMemory.unExMemory}"

structure Samples where
  times : Array Nat := #[]
  total : Nat := 0
  mean : Float := 0
  m2 : Float := 0

def Samples.push (s : Samples) (ns : Nat) : Samples :=
  let n := s.times.size + 1
  let delta := ns.toFloat - s.mean
  let mean := s.mean + delta / n.toFloat
  { times := s.times.push ns, total := s.total + ns, mean,
    m2 := s.m2 + delta * (ns.toFloat - mean) }

/-- Every iteration's result is checked outside its timer. Warm-up has five iterations;
measurement lasts at least `measureMs` and has at least 50 samples. -/
def measure (run : IO Outcome) (expected : Outcome) (measureMs : Nat) : IO Samples := do
  for _ in [:5] do
    unless (← run) == expected do
      throw (IO.userError "warm-up outcome changed")
  let mut samples : Samples := {}
  repeat
    let start ← IO.monoNanosNow
    let outcome ← run
    let elapsed := (← IO.monoNanosNow) - start
    unless outcome == expected do
      throw (IO.userError "timed outcome changed")
    samples := samples.push elapsed
    if samples.times.size >= 50 && samples.total >= measureMs * 1_000_000 then
      break
  return samples

def Samples.csv (s : Samples) (name : String) : String := Id.run do
  let times := s.times.qsort (· < ·)
  let n := times.size
  let median := if n % 2 == 0 then
      (times[n / 2 - 1]!.toFloat + times[n / 2]!.toFloat) / 2
    else times[n / 2]!.toFloat
  let stddev := if n > 1 then Float.sqrt (max 0 (s.m2 / (n - 1).toFloat)) else 0
  -- The common CSV/report loader requires integer nanoseconds. Round derived statistics
  -- only at serialization; retain full precision while accumulating the samples.
  let ns (value : Float) : UInt64 := (value + 0.5).toUInt64
  return s!"{vm},{csvField name},{ns s.mean},{ns median},{times[0]!},{times[n - 1]!},{ns stddev},{n}"

def time (path : System.FilePath) (loops : List String) (measureMs maxSteps : Nat) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let program ← IO.ofExcept (decode bytes)
  let expected ← runEval program maxSteps
  unless expected.ok do
    throw (IO.userError "CEK evaluation failed before timing")
  -- D3 always precedes eval, regardless of the order of the requested loops.
  for loop in ["d3", "eval"] do
    if loops.contains loop then
      IO.println s!"PVB_LOOP {loop} {scriptName path}"
      (← IO.getStdout).flush
      let run := if loop == "d3" then runD3 bytes maxSteps else runEval program maxSteps
      let samples ← measure run expected measureMs
      IO.println s!"PVB_RESULT {loop} {samples.csv (scriptName path)}"
      (← IO.getStdout).flush

def positiveNat (label value : String) : Except String Nat := do
  let some n := value.toNat? | throw s!"invalid {label}: {value}"
  if n == 0 then throw s!"{label} must be positive"
  return n

inductive Command where
  | check : System.FilePath → Nat → Command
  | time : System.FilePath → List String → Nat → Nat → Command

def parseTime (path loops ms : String) (maxSteps : Nat) : Except String Command := do
  let loops := loops.splitOn ","
  unless loops.all (fun s => s == "d3" || s == "eval") do
    throw "LOOPS must be a comma list of d3 and eval"
  return .time path loops (← positiveNat "MEASURE_MS" ms) maxSteps

def parseArgs : List String → Except String Command
  | ["check", path] => .ok (.check path defaultMaxSteps)
  | ["check", path, steps] => do
    return .check path (← positiveNat "MAX_STEPS" steps)
  | ["time", path, loops, ms] => parseTime path loops ms defaultMaxSteps
  | ["time", path, loops, ms, steps] => do
    parseTime path loops ms (← positiveNat "MAX_STEPS" steps)
  | _ => .error "usage: bench_cek check FILE [MAX_STEPS]\n       bench_cek time FILE d3,eval MEASURE_MS [MAX_STEPS]"

end Benchmark.Cek

def main (args : List String) : IO UInt32 := do
  match Benchmark.Cek.parseArgs args with
  | .error message =>
    IO.eprintln message
    return 2
  | .ok command =>
    try
      match command with
      | .check path steps => Benchmark.Cek.check path steps
      | .time path loops ms steps => Benchmark.Cek.time path loops ms steps
      return 0
    catch error =>
      IO.eprintln s!"EVAL_FAIL: {error}"
      return 1
