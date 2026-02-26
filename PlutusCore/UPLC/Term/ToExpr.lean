import PlutusCore.ToExpr
import PlutusCore.UPLC.Term.Basic

namespace PlutusCore.UPLC.Term

open Lean

instance : ToExpr AtomicType where
  toTypeExpr := .const ``AtomicType []
  toExpr
    | .TypeInteger    => .const ``AtomicType.TypeInteger    []
    | .TypeByteString => .const ``AtomicType.TypeByteString []
    | .TypeString     => .const ``AtomicType.TypeString     []
    | .TypeBool       => .const ``AtomicType.TypeBool       []
    | .TypeUnit       => .const ``AtomicType.TypeUnit       []
    | .TypeData       => .const ``AtomicType.TypeData       []

mutual
  def BuiltinType.toExpr : BuiltinType → Expr
    | .AtomicType   a => .app (.const ``BuiltinType.AtomicType   []) (toExpr a)
    | .TypeOperator t => .app (.const ``BuiltinType.TypeOperator []) (TypeOperator.toExpr t)

  def TypeOperator.toExpr : TypeOperator → Expr
    | .TypeList b     =>  .app  (.const ``TypeOperator.TypeList []) (BuiltinType.toExpr b)
    | .TypePair b₁ b₂ => mkApp2 (.const ``TypeOperator.TypePair []) (BuiltinType.toExpr b₁) (BuiltinType.toExpr b₂)
end

instance : ToExpr BuiltinType where
  toTypeExpr := .const ``BuiltinType []
  toExpr     := BuiltinType.toExpr

instance : ToExpr TypeOperator where
  toTypeExpr := .const ``TypeOperator []
  toExpr     := TypeOperator.toExpr

partial def constToExpr : Const → Expr
  | .Integer              i => .app (.const ``Const.Integer              []) (toExpr i)
  | .ByteString           b => .app (.const ``Const.ByteString           []) (toExpr b)
  | .String               s => .app (.const ``Const.String               []) (toExpr s)
  | .Unit                   =>       .const ``Const.Unit                 []
  | .Bool                 b => .app (.const ``Const.Bool                 []) (toExpr b)
  | .ConstList            l => .app (.const ``Const.ConstList            []) (listToExpr (α := Const) (.const ``Const []) constToExpr l)
  | .ConstDataList        l => .app (.const ``Const.ConstDataList        []) (toExpr l)
  | .ConstPairDataList    l => .app (.const ``Const.ConstPairDataList    []) (toExpr l)
  | .Pair                 p => .app (.const ``Const.Pair                 []) (pairToExpr (α := Const) (β := Const) (.const ``Const []) (.const ``Const []) constToExpr constToExpr p)
  | .PairData             p => .app (.const ``Const.PairData             []) (toExpr p)
  | .Data                 d => .app (.const ``Const.Data                 []) (toExpr d)
  | .Bls12_381_G1_element   =>       .const ``Const.Bls12_381_G1_element []
  | .Bls12_381_G2_element   =>       .const ``Const.Bls12_381_G2_element []
  | .Bls12_381_MlResult     =>       .const ``Const.Bls12_381_MlResult   []

instance : ToExpr Const where
  toTypeExpr := .const ``Const []
  toExpr     := constToExpr

instance : ToExpr BuiltinFun where
  toTypeExpr := .const ``BuiltinFun []
  toExpr
    | .AddInteger                      => .const ``BuiltinFun.AddInteger []
    | .SubtractInteger                 => .const ``BuiltinFun.SubtractInteger []
    | .MultiplyInteger                 => .const ``BuiltinFun.MultiplyInteger []
    | .DivideInteger                   => .const ``BuiltinFun.DivideInteger []
    | .QuotientInteger                 => .const ``BuiltinFun.QuotientInteger []
    | .RemainderInteger                => .const ``BuiltinFun.RemainderInteger []
    | .ModInteger                      => .const ``BuiltinFun.ModInteger []
    | .EqualsInteger                   => .const ``BuiltinFun.EqualsInteger []
    | .LessThanInteger                 => .const ``BuiltinFun.LessThanInteger []
    | .LessThanEqualsInteger           => .const ``BuiltinFun.LessThanEqualsInteger []
    | .AppendByteString                => .const ``BuiltinFun.AppendByteString []
    | .ConsByteString                  => .const ``BuiltinFun.ConsByteString []
    | .SliceByteString                 => .const ``BuiltinFun.SliceByteString []
    | .LengthOfByteString              => .const ``BuiltinFun.LengthOfByteString []
    | .IndexByteString                 => .const ``BuiltinFun.IndexByteString []
    | .EqualsByteString                => .const ``BuiltinFun.EqualsByteString []
    | .LessThanByteString              => .const ``BuiltinFun.LessThanByteString []
    | .LessThanEqualsByteString        => .const ``BuiltinFun.LessThanEqualsByteString []
    | .Sha2_256                        => .const ``BuiltinFun.Sha2_256 []
    | .Sha3_256                        => .const ``BuiltinFun.Sha3_256 []
    | .Blake2b_256                     => .const ``BuiltinFun.Blake2b_256 []
    | .VerifyEd25519Signature          => .const ``BuiltinFun.VerifyEd25519Signature []
    | .AppendString                    => .const ``BuiltinFun.AppendString []
    | .EqualsString                    => .const ``BuiltinFun.EqualsString []
    | .EncodeUtf8                      => .const ``BuiltinFun.EncodeUtf8 []
    | .DecodeUtf8                      => .const ``BuiltinFun.DecodeUtf8 []
    | .IfThenElse                      => .const ``BuiltinFun.IfThenElse []
    | .ChooseUnit                      => .const ``BuiltinFun.ChooseUnit []
    | .Trace                           => .const ``BuiltinFun.Trace []
    | .FstPair                         => .const ``BuiltinFun.FstPair []
    | .SndPair                         => .const ``BuiltinFun.SndPair []
    | .ChooseList                      => .const ``BuiltinFun.ChooseList []
    | .MkCons                          => .const ``BuiltinFun.MkCons []
    | .HeadList                        => .const ``BuiltinFun.HeadList []
    | .TailList                        => .const ``BuiltinFun.TailList []
    | .NullList                        => .const ``BuiltinFun.NullList []
    | .ChooseData                      => .const ``BuiltinFun.ChooseData []
    | .ConstrData                      => .const ``BuiltinFun.ConstrData []
    | .MapData                         => .const ``BuiltinFun.MapData []
    | .ListData                        => .const ``BuiltinFun.ListData []
    | .IData                           => .const ``BuiltinFun.IData []
    | .BData                           => .const ``BuiltinFun.BData []
    | .UnConstrData                    => .const ``BuiltinFun.UnConstrData []
    | .UnMapData                       => .const ``BuiltinFun.UnMapData []
    | .UnListData                      => .const ``BuiltinFun.UnListData []
    | .UnIData                         => .const ``BuiltinFun.UnIData []
    | .UnBData                         => .const ``BuiltinFun.UnBData []
    | .EqualsData                      => .const ``BuiltinFun.EqualsData []
    | .MkPairData                      => .const ``BuiltinFun.MkPairData []
    | .MkNilData                       => .const ``BuiltinFun.MkNilData []
    | .MkNilPairData                   => .const ``BuiltinFun.MkNilPairData []
    | .SerializeData                   => .const ``BuiltinFun.SerializeData []
    | .VerifyEcdsaSecp256k1Signature   => .const ``BuiltinFun.VerifyEcdsaSecp256k1Signature []
    | .VerifySchnorrSecp256k1Signature => .const ``BuiltinFun.VerifySchnorrSecp256k1Signature []
    | .Bls12_381_G1_add                => .const ``BuiltinFun.Bls12_381_G1_add []
    | .Bls12_381_G1_neg                => .const ``BuiltinFun.Bls12_381_G1_neg []
    | .Bls12_381_G1_scalarMul          => .const ``BuiltinFun.Bls12_381_G1_scalarMul []
    | .Bls12_381_G1_equal              => .const ``BuiltinFun.Bls12_381_G1_equal []
    | .Bls12_381_G1_hashToGroup        => .const ``BuiltinFun.Bls12_381_G1_hashToGroup []
    | .Bls12_381_G1_compress           => .const ``BuiltinFun.Bls12_381_G1_compress []
    | .Bls12_381_G1_uncompress         => .const ``BuiltinFun.Bls12_381_G1_uncompress []
    | .Bls12_381_G2_add                => .const ``BuiltinFun.Bls12_381_G2_add []
    | .Bls12_381_G2_neg                => .const ``BuiltinFun.Bls12_381_G2_neg []
    | .Bls12_381_G2_scalarMul          => .const ``BuiltinFun.Bls12_381_G2_scalarMul []
    | .Bls12_381_G2_equal              => .const ``BuiltinFun.Bls12_381_G2_equal []
    | .Bls12_381_G2_hashToGroup        => .const ``BuiltinFun.Bls12_381_G2_hashToGroup []
    | .Bls12_381_G2_compress           => .const ``BuiltinFun.Bls12_381_G2_compress []
    | .Bls12_381_G2_uncompress         => .const ``BuiltinFun.Bls12_381_G2_uncompress []
    | .Bls12_381_millerLoop            => .const ``BuiltinFun.Bls12_381_millerLoop []
    | .Bls12_381_mulMlResult           => .const ``BuiltinFun.Bls12_381_mulMlResult []
    | .Bls12_381_finalVerify           => .const ``BuiltinFun.Bls12_381_finalVerify []
    | .Keccak_256                      => .const ``BuiltinFun.Keccak_256 []
    | .Blake2b_224                     => .const ``BuiltinFun.Blake2b_224 []
    | .IntegerToByteString             => .const ``BuiltinFun.IntegerToByteString []
    | .ByteStringToInteger             => .const ``BuiltinFun.ByteStringToInteger []
    | .AndByteString                   => .const ``BuiltinFun.AndByteString []
    | .OrByteString                    => .const ``BuiltinFun.OrByteString []
    | .XorByteString                   => .const ``BuiltinFun.XorByteString []
    | .ComplementByteString            => .const ``BuiltinFun.ComplementByteString []
    | .ReadBit                         => .const ``BuiltinFun.ReadBit []
    | .WriteBits                       => .const ``BuiltinFun.WriteBits []
    | .ReplicateByte                   => .const ``BuiltinFun.ReplicateByte []
    | .ShiftByteString                 => .const ``BuiltinFun.ShiftByteString []
    | .RotateByteString                => .const ``BuiltinFun.RotateByteString []
    | .CountSetBits                    => .const ``BuiltinFun.CountSetBits []
    | .FindFirstSetBit                 => .const ``BuiltinFun.FindFirstSetBit []
    | .Ripemd_160                      => .const ``BuiltinFun.Ripemd_160 []
    | .ExpModInteger                   => .const ``BuiltinFun.ExpModInteger []

partial def termToExpr : PlutusCore.UPLC.Term.Term → Expr
  | .Var     s   =>  .app  (.const ``Term.Var     []) (toExpr s)
  | .Const   c   =>  .app  (.const ``Term.Const   []) (toExpr c)
  | .Builtin b   =>  .app  (.const ``Term.Builtin []) (toExpr b)
  | .Lam     x b => mkApp2 (.const ``Term.Lam     []) (toExpr x)     (termToExpr b)
  | .Apply   f x => mkApp2 (.const ``Term.Apply   []) (termToExpr f) (termToExpr x)
  | .Delay   t   =>  .app  (.const ``Term.Delay   []) (termToExpr t)
  | .Force   t   =>  .app  (.const ``Term.Force   []) (termToExpr t)
  | .Constr  i f => mkApp2 (.const ``Term.Constr  []) (toExpr i)     (listToExpr (α := PlutusCore.UPLC.Term.Term) (.const ``Term.Term []) termToExpr f)
  | .Case    t c => mkApp2 (.const ``Term.Case    []) (termToExpr t) (listToExpr (α := PlutusCore.UPLC.Term.Term) (.const ``Term.Term []) termToExpr c)
  | .Error       =>         .const ``Term.Error   []

instance : ToExpr PlutusCore.UPLC.Term.Term where
  toTypeExpr := .const ``PlutusCore.UPLC.Term.Term []
  toExpr     := termToExpr

instance : ToExpr Version where
  toTypeExpr := .const ``Version []
  toExpr v   := mkApp3 (.const ``Version.Version []) (mkRawNatLit v.1) (mkRawNatLit v.2) (mkRawNatLit v.3)

instance : ToExpr Program where
  toTypeExpr := .const ``Program []
  toExpr | .Program v t => mkApp2 (.const ``Program.Program []) (toExpr v) (toExpr t)

end PlutusCore.UPLC.Term
