import Lean.Data.Json

namespace Benchmark.PrepUplc

/-- The native execution outcome, independent of its report representation. -/
inductive NativeOutcome where
  | halted
  | failed
  | exhausted
  /-- A nonterminal native result that disagrees with the independent step counter.
      Retained for diagnostic and historical reports. -/
  | running
  deriving BEq, Inhabited, Repr

/-- Stable labels used in JSON, CSV and human-readable reports. -/
def NativeOutcome.label : NativeOutcome → String
  | .halted    => "halt"
  | .failed    => "error"
  | .exhausted => "exhausted"
  | .running   => "running"

instance : ToString NativeOutcome := ⟨NativeOutcome.label⟩

instance : Lean.ToJson NativeOutcome where
  toJson outcome := .str outcome.label

instance : Lean.FromJson NativeOutcome where
  fromJson? json := do
    match ← json.getStr? with
    | "halt"      => return .halted
    | "error"     => return .failed
    | "exhausted" => return .exhausted
    | "running"   => return .running
    | label       => throw s!"Unknown native execution outcome: {label}"

end Benchmark.PrepUplc
