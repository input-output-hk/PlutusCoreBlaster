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
open PlutusCore.UPLC.FlatEncoding (decodeProgramFromBytes)

def vm : String := "plutuscore-lean"
def defaultMaxSteps : Nat := 100_000_000
def timingHeader : String := "vm,script,mean_ns,median_ns,min_ns,max_ns,stddev_ns,iterations"

def csvField (s : String) : String :=
  if s.contains ',' || s.contains '"' || s.contains '\n' || s.contains '\r' then
    "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else s

def scriptName (path : System.FilePath) : String :=
  path.fileStem.getD path.toString

/-- Raw Flat decoding is included in D3; file I/O is outside the timer. -/
def decode (bytes : ByteArray) : Except String Program :=
  match decodeProgramFromBytes bytes with
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

end Benchmark.Cek
