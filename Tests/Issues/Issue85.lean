import Blaster
import PlutusCore.UPLC

-- https://github.com/input-output-hk/PlutusCoreBlaster/issues/85
--
-- The costs of `appendString`, `equalsString` and `encodeUtf8` depend on the
-- sizes of their string arguments. Plutus 1.64 measures a string argument by
-- its number of characters under semantics variants A–C (`ExMemoryUsage Text`),
-- and by its UTF-8 length in bytes divided by 4, rounded down, under D and E
-- (`TextCostedByByteLength`). Each argument is measured on its own.
--
-- Every expected budget below is what Plutus 1.64.0.0's
-- `uplc evaluate --counting -S <variant>` reports for the same program.
namespace Tests.Issue85

open PlutusCore.Default (BuiltinSemanticsVariant PlutusVersion ProtocolVersion)
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.CostModels (builtinCostSelected constSize textByteLengthSize)
open PlutusCore.UPLC.ExBudget (ExBudget)
open PlutusCore.UPLC.Term (BuiltinFun Const Program Term)

/-! ## String sizes -/

-- `(string, characters, UTF-8 bytes ÷ 4)`
private def sizes : List (String × Nat × Nat) :=
  [ ("", 0, 0), ("abcd", 4, 1), ("abcdefghijkl", 12, 3), ("aé", 2, 0)
  , ("日本", 2, 1), ("日本語の", 4, 3), ("😀", 1, 1) ]

/-- info: [] -/
#guard_msgs in #eval sizes.filter fun (s, chars, bytes) =>
  constSize (.String s) != chars || textByteLengthSize s != bytes

/-! ## Budgets

Each program applies one builtin to string constants. At the default (current
mainnet) protocol version, V1/V2 run variant D and V3 runs E. At `.preConway`,
V1/V2 run A and V3 runs C. -/

/-- `[(builtin b) (con string s₁) … (con string sₙ)]` -/
private def call (b : BuiltinFun) (args : List String) : Program :=
  .Program (.Version 1 0 0) (args.foldl (fun f s => .Apply f (.Const (.String s))) (.Builtin b))

private def budget : ExBudget := ⟨⟨10_000_000_000⟩, ⟨100_000_000⟩⟩

/-- The `(cpu, mem)` a successful run spent. -/
private def spent : EvaluationResult → Option (Nat × Nat)
  | .Success _ b => some (b.exBudgetCPU.unExCPU, b.exBudgetMemory.unExMemory)
  | _ => none

private def runs : List (Char × PlutusVersion × ProtocolVersion) :=
  [ ('A', .plutusV1, .preConway), ('C', .plutusV3, .preConway)
  , ('D', .plutusV1, default), ('E', .plutusV3, default) ]

private structure Case where
  builtin  : BuiltinFun
  args     : List String
  /-- `(cpu, mem)` under variants A, C, D and E. -/
  expected : List (Nat × Nat)

/-- The runs whose budget differs from the expected one, with the budget. -/
private def mismatches (cases : List Case) : List String :=
  cases.flatMap fun c => (runs.zip c.expected).filterMap fun ((v, plutus, protocol), e) =>
    let got := spent (cekExecuteProgramWithBudget (call c.builtin c.args) plutus protocol [] budget)
    if got == some e then none
    else some s!"{repr c.builtin} {c.args} under {v}: expected {e}, got {got}"

private def cases : List Case :=
  [ ⟨.EncodeUtf8, [""], [(70100, 404), (49100, 404), (49100, 404), (49100, 404)]⟩
  , ⟨.EncodeUtf8, ["abcd"], [(184748, 412), (220784, 412), (92021, 406), (92021, 406)]⟩
  , ⟨.EncodeUtf8, ["abcdefghijkl"], [(414044, 428), (564152, 428), (177863, 410), (177863, 410)]⟩
  , ⟨.EncodeUtf8, ["aé"], [(127424, 408), (134942, 408), (49100, 404), (49100, 404)]⟩
  , ⟨.EncodeUtf8, ["日本"], [(127424, 408), (134942, 408), (92021, 406), (92021, 406)]⟩
  , ⟨.EncodeUtf8, ["日本語の"], [(184748, 412), (220784, 412), (177863, 410), (177863, 410)]⟩
  , ⟨.EncodeUtf8, ["😀"], [(98762, 406), (92021, 406), (92021, 406), (92021, 406)]⟩
  , ⟨.AppendString, ["", ""], [(116100, 604), (81100, 604), (81100, 604), (81100, 604)]⟩
    -- Under D/E each argument rounds down to 0 on its own, though together
    -- they have 5 bytes.
  , ⟨.AppendString, ["abc", "de"], [(236985, 609), (380885, 609), (81100, 604), (81100, 604)]⟩
  , ⟨.AppendString, ["日本語の", "abcd"], [(309516, 612), (560756, 612), (320928, 608), (320928, 608)]⟩
    -- `equalsString` costs more when its arguments have the same size: these
    -- are the same size only under D/E (3 and 3, but 4 and 12 characters)…
  , ⟨.EqualsString, ["日本語の", "abcdefghijkl"],
      [(302100, 601), (119284, 601), (262882, 601), (262882, 601)]⟩
    -- …and these only under A–C (4 and 4 characters, but 1 and 3).
  , ⟨.EqualsString, ["abcd", "日本語の"], [(328092, 601), (323476, 601), (119284, 601), (119284, 601)]⟩
  , ⟨.EqualsString, ["日本語の", "日本語の"],
      [(328092, 601), (323476, 601), (262882, 601), (262882, 601)]⟩
  , ⟨.EqualsString, ["", ""], [(116100, 601), (81100, 601), (81100, 601), (81100, 601)]⟩ ]

-- `#eval!`: the budgeted machine's termination proof is `sorry`.
/-- info: [] -/
#guard_msgs in #eval! mismatches cases

-- Variant B (V1/V2 at protocol versions 9–10) has no protocol version here
-- yet (#86). For every program above 1.64 charges the same under B as under
-- C, so B's builtin costs are checked against C's.
#guard cases.all fun c =>
  let args := (c.args.map fun s => CekValue.VCon (.String s)).reverse
  builtinCostSelected .defaultFunSemanticsVariantB c.builtin args ==
    builtinCostSelected .defaultFunSemanticsVariantC c.builtin args

/-! ## Symbolic strings -/

example : ∀ s : String,
  builtinCostSelected .defaultFunSemanticsVariantC .EncodeUtf8 [.VCon (.String s)] =
    ⟨⟨1000 + 42921 * s.length⟩, ⟨4 + 2 * s.length⟩⟩ := by blaster

example : ∀ s : String,
  builtinCostSelected .defaultFunSemanticsVariantE .EncodeUtf8 [.VCon (.String s)] =
    ⟨⟨1000 + 42921 * (s.utf8ByteSize / 4)⟩, ⟨4 + 2 * (s.utf8ByteSize / 4)⟩⟩ := by blaster

example : ∀ s t : String,
  builtinCostSelected .defaultFunSemanticsVariantE .AppendString [.VCon (.String t), .VCon (.String s)] =
    ⟨⟨1000 + 59957 * (s.utf8ByteSize / 4 + t.utf8ByteSize / 4)⟩,
      ⟨4 + (s.utf8ByteSize / 4 + t.utf8ByteSize / 4)⟩⟩ := by blaster

end Tests.Issue85
