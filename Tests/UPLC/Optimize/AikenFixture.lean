import PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Tests.AikenValidationFixture

def bytes (ns : List Nat) : ByteString := ⟨String.mk (ns.map Char.ofNat)⟩

def script : Program := .Program (.Version 1 1 0) (.Lam (.Case (.Constr 0 [(.Force (.Builtin .TailList)), (.Force (.Builtin .HeadList)), (.Force (.Builtin .MkCons)), (.Force (.Force (.Builtin .ChooseList))), (.Force (.Force (.Builtin .SndPair))), (.Force (.Force (.Builtin .FstPair))), (.Force (.Builtin .IfThenElse))]) [(.Lam (.Lam (.Lam (.Lam (.Lam (.Lam (.Lam (.Force (.Case (.Constr 0 [(.Apply (.Lam (.Apply (.Lam (.Apply (.Apply (.Lam (.Lam (.Force (.Case (.Constr 0 [(.Apply (.Apply (.Builtin .EqualsInteger) (.Const (.Integer 1))) (.Apply (.Var 5) (.Apply (.Builtin .UnConstrData) (.Var 0)))), (.Delay (.Apply (.Lam (.Case (.Constr 0 [(.Apply (.Var 10) (.Var 0)), (.Apply (.Var 10) (.Apply (.Var 11) (.Var 0))), (.Lam (.Lam (.Force (.Case (.Constr 0 [(.Var 0), (.Delay (.Const (.Bool false))), (.Delay (.Force (.Case (.Constr 0 [(.Apply (.Apply (.Builtin .EqualsByteString) (.Apply (.Builtin .UnBData) (.Apply (.Var 12) (.Var 0)))) (.Const (.ByteString (bytes [17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17])))), (.Delay (.Const (.Bool true))), (.Delay (.Apply (.Apply (.Var 1) (.Var 1)) (.Apply (.Var 13) (.Var 0))))]) [(.Var 7)])))]) [(.Var 10)]))))]) [(.Lam (.Lam (.Lam (.Apply (.Apply (.Var 0) (.Var 0)) (.Apply (.Lam (.Apply (.Apply (.Var 0) (.Var 0)) (.Apply (.Builtin .UnListData) (.Apply (.Var 14) (.Apply (.Var 15) (.Apply (.Var 15) (.Apply (.Var 15) (.Apply (.Var 15) (.Apply (.Var 15) (.Apply (.Var 15) (.Apply (.Var 15) (.Apply (.Var 15) (.Apply (.Var 11) (.Apply (.Builtin .UnConstrData) (.Apply (.Var 14) (.Var 8)))))))))))))))) (.Lam (.Lam (.Force (.Case (.Constr 0 [(.Var 0), (.Delay (.Const (.ConstDataList []))), (.Delay (.Apply (.Lam (.Force (.Case (.Constr 0 [(.Apply (.Apply (.Builtin .EqualsInteger) (.Const (.Integer 28))) (.Apply (.Builtin .LengthOfByteString) (.Var 0))), (.Delay (.Apply (.Apply (.Var 15) (.Apply (.Builtin .BData) (.Var 0))) (.Apply (.Apply (.Var 2) (.Var 2)) (.Apply (.Var 17) (.Var 1))))), (.Delay .Error)]) [(.Var 11)]))) (.Apply (.Builtin .UnBData) (.Apply (.Var 15) (.Var 0)))))]) [(.Var 13)])))))))))])) (.Apply (.Var 6) (.Apply (.Builtin .UnConstrData) (.Var 0))))), (.Delay (.Const (.Bool false)))]) [(.Var 4)])))) (.Apply (.Var 7) (.Var 0))) (.Apply (.Var 7) (.Apply (.Var 8) (.Var 0))))) (.Apply (.Var 7) (.Var 0)))) (.Apply (.Var 2) (.Apply (.Builtin .UnConstrData) (.Var 7)))), (.Delay (.Const .Unit)), (.Delay (.Apply .Error (.Force .Error)))]) [(.Var 0)])))))))))]))

def context (signers : List Data) : Data :=
  .Constr 0 [.Constr 0 [.List [], .List [], .List [], .I 0, .Map [], .List [],
    .Map [], .I 0, .List signers, .Map [], .Map [], .B (bytes (List.replicate 32 0)),
    .Map [], .List [], .Constr 1 [], .Constr 1 []], .I 0,
    .Constr 1 [.Constr 0 [.B (bytes (List.replicate 32 0)), .I 0], .Constr 1 []]]

def params (signers : List Data) : List Term := [.Const (.Data (context signers))]

def start (signers : List Data) : State :=
  match script with
  | .Program _ body => initialState (applyParams body (params signers))

end Tests.AikenValidationFixture
