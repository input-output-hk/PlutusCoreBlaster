import PlutusCore.UPLC

/-! # Builtin arguments that cannot be read

When a builtin call is saturated, Plutus 1.64 reads ("unlifts") its arguments
before it costs the call. If an argument cannot be read, the call fails and
costs nothing; if the builtin fails after reading its arguments, it is charged
in full (see `PlutusCore/UPLC/BuiltinFunctions/Unlifting.lean`).

Every `charged` value below is what Plutus 1.64.0.0's
`uplc evaluate -R 100:100 -S <variant>` gives for the same call: with a budget
that covers only the startup cost, a charged call overspends, and a call that
is not charged fails with an evaluation error.
-/

namespace Tests.UPLC.BuiltinUnlifting

open PlutusCore.Default (BuiltinSemanticsVariant)
open PlutusCore.UPLC.Builtins (ExpectedBuiltinArg ExpectedBuiltinArgs expectedArgs)
open PlutusCore.UPLC.BuiltinFunctions.Evaluate (evaluateBuiltinFunction)
open PlutusCore.UPLC.BuiltinFunctions.Unlifting (argTypes)
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.ExBudget (ExBudget)
open PlutusCore.UPLC.FlatEncoding.Internal (builtinTable)
open PlutusCore.UPLC.Term (BuiltinFun Const Program Term)

private def variants : List BuiltinSemanticsVariant :=
  [ .defaultFunSemanticsVariantA, .defaultFunSemanticsVariantB, .defaultFunSemanticsVariantC
  , .defaultFunSemanticsVariantD, .defaultFunSemanticsVariantE ]

/-! ## Every builtin has one argument type per argument -/

private def termArgs : ExpectedBuiltinArgs → Nat
  | .One a => if a == .ArgV then 1 else 0
  | .More a r => (if a == .ArgV then 1 else 0) + termArgs r

/-- info: [] -/
#guard_msgs in #eval builtinTable.filterMap fun (_, b) =>
  if variants.all fun v => (argTypes v b).length == termArgs (expectedArgs b) then none
  else some (reprStr b)

/-! ## Calls, and whether 1.64 charges them -/

private def int (n : Int) : CekValue := .VCon (.Integer n)
private def bs (s : String) : CekValue := .VCon (.ByteString ⟨s⟩)
private def unit : CekValue := .VCon .Unit
private def bool (b : Bool) : CekValue := .VCon (.Bool b)
private def str (s : String) : CekValue := .VCon (.String s)
private def ints (ns : List Int) : CekValue := .VCon (.ConstList (ns.map .Integer))
/-- `(lam x x)`: a value, but not a constant. -/
private def lam : CekValue := .VLam (.Var 0) []

private structure Case where
  name    : String
  variant : BuiltinSemanticsVariant
  builtin : BuiltinFun
  /-- The arguments, first argument first. -/
  args    : List CekValue
  /-- Whether 1.64 charges the builtin's cost. -/
  charged : Bool

private def cases : List Case :=
  [ -- An argument of the wrong type is not charged.
    ⟨"sha3_256 \"a\"", .defaultFunSemanticsVariantE, .Sha3_256, [str "a"], false⟩
  , ⟨"sha3_256 \"a\" (A)", .defaultFunSemanticsVariantA, .Sha3_256, [str "a"], false⟩
  , ⟨"addInteger () 1", .defaultFunSemanticsVariantE, .AddInteger, [unit, int 1], false⟩
  , ⟨"ifThenElse 1 () ()", .defaultFunSemanticsVariantE, .IfThenElse, [int 1, unit, unit], false⟩
  , ⟨"chooseUnit 1 ()", .defaultFunSemanticsVariantE, .ChooseUnit, [int 1, unit], false⟩
  , ⟨"trace () ()", .defaultFunSemanticsVariantE, .Trace, [unit, unit], false⟩
  , ⟨"iData ()", .defaultFunSemanticsVariantE, .IData, [unit], false⟩
  , ⟨"insertCoin # # 1 ()", .defaultFunSemanticsVariantE, .InsertCoin,
      [bs "", bs "", int 1, unit], false⟩
  , ⟨"constrData 0 [1]", .defaultFunSemanticsVariantE, .ConstrData, [int 0, ints [1]], false⟩
  , ⟨"mapData ([] : list data)", .defaultFunSemanticsVariantE, .MapData,
      [.VCon (.ConstDataList [])], false⟩
  , ⟨"writeBits #00 [True] True", .defaultFunSemanticsVariantE, .WriteBits,
      [bs "\x00", .VCon (.ConstList [.Bool true]), bool true], false⟩
    -- A polymorphic argument must be a constant, unless it is a type variable.
  , ⟨"headList (lam x x)", .defaultFunSemanticsVariantE, .HeadList, [lam], false⟩
  , ⟨"ifThenElse True (lam x x) (lam x x)", .defaultFunSemanticsVariantE, .IfThenElse,
      [bool true, lam, lam], true⟩
    -- A failure after the arguments are read is charged, including a polymorphic
    -- constant of the wrong shape, which the builtin itself rejects.
  , ⟨"headList 1", .defaultFunSemanticsVariantE, .HeadList, [int 1], true⟩
  , ⟨"headList []", .defaultFunSemanticsVariantE, .HeadList, [ints []], true⟩
  , ⟨"fstPair ()", .defaultFunSemanticsVariantE, .FstPair, [unit], true⟩
  , ⟨"mkCons 1 [True]", .defaultFunSemanticsVariantE, .MkCons,
      [int 1, .VCon (.ConstList [.Bool true])], true⟩
  , ⟨"divideInteger 1 0", .defaultFunSemanticsVariantE, .DivideInteger, [int 1, int 0], true⟩
  , ⟨"lengthOfArray [1]", .defaultFunSemanticsVariantE, .LengthOfArray, [ints [1]], true⟩
    -- `Int` arguments: [-2^63, 2^63 - 1], in every variant.
  , ⟨"sliceByteString (2^63 - 1) 1 #00 (A)", .defaultFunSemanticsVariantA, .SliceByteString,
      [int (2^63 - 1), int 1, bs "\x00"], true⟩
  , ⟨"sliceByteString 2^63 1 #00 (A)", .defaultFunSemanticsVariantA, .SliceByteString,
      [int (2^63), int 1, bs "\x00"], false⟩
  , ⟨"sliceByteString (-2^63) 1 #00 (A)", .defaultFunSemanticsVariantA, .SliceByteString,
      [int (-2^63), int 1, bs "\x00"], true⟩
  , ⟨"sliceByteString (-2^63 - 1) 1 #00 (A)", .defaultFunSemanticsVariantA, .SliceByteString,
      [int (-2^63 - 1), int 1, bs "\x00"], false⟩
  , ⟨"indexArray [1] 2^63", .defaultFunSemanticsVariantE, .IndexArray,
      [.VCon (.ConstArray [.Integer 1]), int (2^63)], false⟩
    -- `Word8`: `consByteString` under C and E, `replicateByte`'s byte.
  , ⟨"consByteString 255 # (C)", .defaultFunSemanticsVariantC, .ConsByteString,
      [int 255, bs ""], true⟩
  , ⟨"consByteString 256 # (C)", .defaultFunSemanticsVariantC, .ConsByteString,
      [int 256, bs ""], false⟩
  , ⟨"consByteString (-1) # (C)", .defaultFunSemanticsVariantC, .ConsByteString,
      [int (-1), bs ""], false⟩
  , ⟨"consByteString 256 # (A)", .defaultFunSemanticsVariantA, .ConsByteString,
      [int 256, bs ""], true⟩
  , ⟨"consByteString 256 # (B)", .defaultFunSemanticsVariantB, .ConsByteString,
      [int 256, bs ""], true⟩
  , ⟨"consByteString 256 # (D)", .defaultFunSemanticsVariantD, .ConsByteString,
      [int 256, bs ""], true⟩
  , ⟨"replicateByte 1 256", .defaultFunSemanticsVariantE, .ReplicateByte, [int 1, int 256], false⟩
    -- `Word64`: `constrData`'s index under D and E.
  , ⟨"constrData (2^64 - 1) []", .defaultFunSemanticsVariantE, .ConstrData,
      [int (2^64 - 1), .VCon (.ConstDataList [])], true⟩
  , ⟨"constrData 2^64 []", .defaultFunSemanticsVariantE, .ConstrData,
      [int (2^64), .VCon (.ConstDataList [])], false⟩
  , ⟨"constrData (-1) []", .defaultFunSemanticsVariantE, .ConstrData,
      [int (-1), .VCon (.ConstDataList [])], false⟩
  , ⟨"constrData (-1) [] (C)", .defaultFunSemanticsVariantC, .ConstrData,
      [int (-1), .VCon (.ConstDataList [])], true⟩
    -- The shift amount is an `Int` under D and E, an `Integer` under A–C.
  , ⟨"shiftByteString #00 2^63", .defaultFunSemanticsVariantE, .ShiftByteString,
      [bs "\x00", int (2^63)], false⟩
  , ⟨"shiftByteString #00 2^63 (C)", .defaultFunSemanticsVariantC, .ShiftByteString,
      [bs "\x00", int (2^63)], true⟩ ]

/-- The cases whose cost, or whose failure without a cost, differs from 1.64. -/
private def mismatches : List String :=
  cases.filterMap fun c =>
    let Vs := c.args.reverse
    let charged := builtinCallCost c.variant c.builtin Vs != ExBudget.zero
    -- A call that is not charged must also fail.
    let fails := (evaluateBuiltinFunction c.variant c.builtin Vs).isNone
    if charged == c.charged && (charged || fails) then none
    else some s!"{c.name}: charged {charged}, fails {fails}"

/-- info: [] -/
#guard_msgs in #eval mismatches

/-! ## Through the budgeted machine

The review's example: `sha3_256` applied to a string under a budget that covers
the machine steps but not the builtin. -/

private def sha3 (c : Const) : Program :=
  .Program (.Version 1 1 0) (.Apply (.Builtin .Sha3_256) (.Const c))

private def budget : ExBudget := ⟨⟨100_000⟩, ⟨1_000_000⟩⟩

private def fails : EvaluationResult → Bool
  | .EvaluationError => true
  | _ => false

private def exhausted : EvaluationResult → Bool
  | .BudgetExhausted _ => true
  | _ => false

#guard fails (cekExecuteProgramWithBudget (sha3 (.String "a")) .plutusV3 default [] budget)
#guard fails (cekExecuteProgramWithBudget (sha3 (.String "a")) .plutusV1 .preConway [] budget)
#guard exhausted (cekExecuteProgramWithBudget (sha3 (.ByteString ⟨""⟩)) .plutusV3 default [] budget)

end Tests.UPLC.BuiltinUnlifting
