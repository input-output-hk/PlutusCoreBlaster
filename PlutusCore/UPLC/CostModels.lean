/- Cost model for UPLC DEK Machine evaluation-/
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.ExBudget
import PlutusCore.UPLC.CekValue
import PlutusCore.Integer
import PlutusCore.ByteString
import PlutusCore.Default

namespace PlutusCore.UPLC.CostModels

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.ExBudget
open PlutusCore.UPLC.CekValue
open PlutusCore.Integer
open PlutusCore.Data
open PlutusCore.ByteString
open PlutusCore.Default
structure CekMachineCosts where
  -- startup cost
  startupCost : ExBudget
  -- basic cek steps
  stepCostVar : ExBudget
  stepCostConst : ExBudget
  stepCostLam : ExBudget
  stepCostDelay : ExBudget
  stepCostForce : ExBudget
  stepCostApply : ExBudget
  stepCostBuiltin : ExBudget
  stepCostConstr : ExBudget
  stepCostCase : ExBudget
  -- return cost
  returnCost : ExBudget
deriving Repr, Inhabited

-- Default CEK machine costs
-- https://github.com/IntersectMBO/plutus/tree/master/plutus-core/cost-model/data
def defaultCekMachineCostsA : CekMachineCosts :=
  { startupCost     := { exBudgetCPU := ⟨100⟩   , exBudgetMemory := ⟨100⟩},
    stepCostVar     := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostConst   := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostLam     := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostDelay   := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostForce   := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostApply   := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostBuiltin := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostConstr  := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostCase    := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩},
    returnCost      := { exBudgetCPU := ⟨23000⟩ , exBudgetMemory := ⟨100⟩}
  }

def defaultCekMachineCostsB : CekMachineCosts :=
  { startupCost     := { exBudgetCPU := ⟨100⟩   , exBudgetMemory := ⟨100⟩},
    stepCostVar     := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostConst   := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostLam     := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostDelay   := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostForce   := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostApply   := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostBuiltin := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostConstr  := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostCase    := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    returnCost      := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩}
  }

def defaultCekMachineCostsC : CekMachineCosts :=
  { startupCost     := { exBudgetCPU := ⟨100⟩   , exBudgetMemory := ⟨100⟩},
    stepCostVar     := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostConst   := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostLam     := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostDelay   := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostForce   := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostApply   := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostBuiltin := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostConstr  := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    stepCostCase    := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩},
    returnCost      := { exBudgetCPU := ⟨16000⟩ , exBudgetMemory := ⟨100⟩}
  }

-- Helpers

-- TODO: Either fix something so we can add the real implementation or decide if we're ok with that
/-- Blaster friendly Integer size-/
def integerSize (i : Integer) : Nat :=
  let n := i.natAbs
  if n < 18446744073709551616 then 1                                                                                                                                                                                                    --  2^64
  else if n < 340282366920938463463374607431768211456 then 2                                                                                                                                                                            --  2^128
  else if n < 6277101735386680763835789423207666416102355444464034512896 then 3                                                                                                                                                         --  2^192
  else if n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 then 4                                                                                                                                     --  2^256
  else if n < 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 then 5                                                                                                                  --  2^320
  else if n < 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 then 6                                                                                               --  2^384
  else if n < 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656 then 7                                                                           --  2^448
  else 8


/-- Calculate the size ofa bytestring -/
def byteStringSize (bs : ByteString) : Nat :=
  let byteLen := (bs.data.length + 7) / 8 -- round up
  byteLen

mutual

  def listDataSize (ds : List Data) : Nat :=
    let rec loop (acc : Nat) : List Data → Nat
      | h :: t => loop (acc + dataSize h) t
      | []     => acc
    loop 0 ds

  def pairsDataSize (kvs : List (Data × Data)) : Nat :=
    let rec loop (acc : Nat) : List (Data × Data) → Nat
      | (p1, p2) :: t => loop (acc + dataSize p1 + dataSize p2) t
      | []       => acc
    loop 0 kvs

  /-- Size of a data value -/
  def dataSize (d : Data) : Nat :=
    match h : d with
    | Data.Constr n ds => 1 + listDataSize ds
    | Data.Map    kvs  => 1 + pairsDataSize kvs
    | Data.List   ds   => 1 + listDataSize ds
    | Data.I      i    => 1 + integerSize i
    | Data.B      bs   => 1 + byteStringSize bs

end

/-- Size of a const value-/
def constSize (c : Const) : Nat :=
  match c with
  | Const.Integer i => integerSize i
  | Const.ByteString bs => byteStringSize bs
  | Const.String s => s.length
  | Const.Unit => 0
  | Const.Bool _ => 1
  | Const.ConstList cs => cs.foldl (fun acc c => acc + constSize c) 0
  | Const.ConstDataList ds => ds.foldl (fun acc d => acc + dataSize d) 0
  | Const.ConstPairDataList ps => ps.foldl (fun acc (d1, d2) => acc + dataSize d1 + dataSize d2) 0
  | Const.ConstArray cs => cs.foldl (fun acc c => acc + constSize c) 0
  | Const.Pair (c1, c2) => constSize c1 + constSize c2
  | Const.PairData (d1, d2) => dataSize d1 + dataSize d2
  | Const.Data d => dataSize d
  | Const.Bls12_381_G1_element => 48
  | Const.Bls12_381_G2_element => 96
  | Const.Bls12_381_MlResult => 576

def cekValueSize (v : CekValue) : Nat :=
  match v with
    | CekValue.VCon c => constSize c
    | _ => 1

def argSize (args : List CekValue) (i : Nat) : Nat :=
  if h : i < args.length then cekValueSize (args.get ⟨i, h⟩) else 1 -- 1?

def maxArgSize (args : List CekValue) : Nat :=
  match args.map cekValueSize with
  | [] => 1 -- 1?
  | sizes => sizes.foldl max 1

def minArgSize (args : List CekValue) : Nat :=
  match args.map cekValueSize with
  | [] => 1 -- 1?
  | sizes => sizes.foldl min (sizes.head!)

def addedArgSize (args : List CekValue) : Nat :=
  args.foldl (fun acc arg => acc + cekValueSize arg) 0

-- BuiltinCosts
-- Auto-generated by scripts/gen_builtin_costs.py from builtinCostModelA.json
-- Source: https://github.com/IntersectMBO/plutus/tree/master/plutus-core/cost-model/data/
def builtinCostsA (b : BuiltinFun) (args : List CekValue) : ExBudget :=
  match b with
  | BuiltinFun.AddInteger =>
    ⟨⟨205665 + 812 * maxArgSize args⟩, ⟨1 + 1 * maxArgSize args⟩⟩
  | BuiltinFun.AppendByteString =>
    ⟨⟨1000 + 571 * addedArgSize args⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.AppendString =>
    ⟨⟨1000 + 24177 * addedArgSize args⟩, ⟨4 + 1 * addedArgSize args⟩⟩
  | BuiltinFun.BData =>
    ⟨⟨1000⟩, ⟨32⟩⟩
  | BuiltinFun.Blake2b_224 =>
    ⟨⟨207616 + 8310 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Blake2b_256 =>
    ⟨⟨117366 + 10475 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Bls12_381_G1_add =>
    ⟨⟨962335⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_compress =>
    ⟨⟨2780678⟩, ⟨6⟩⟩
  | BuiltinFun.Bls12_381_G1_equal =>
    ⟨⟨442008⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G1_hashToGroup =>
    ⟨⟨52538055 + 3756 * argSize args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_neg =>
    ⟨⟨267929⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_scalarMul =>
    ⟨⟨76433006 + 8868 * argSize args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_uncompress =>
    ⟨⟨52948122⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_add =>
    ⟨⟨1995836⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_compress =>
    ⟨⟨3227919⟩, ⟨12⟩⟩
  | BuiltinFun.Bls12_381_G2_equal =>
    ⟨⟨901022⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G2_hashToGroup =>
    ⟨⟨166917843 + 4307 * argSize args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_neg =>
    ⟨⟨284546⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_scalarMul =>
    ⟨⟨158221314 + 26549 * argSize args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_uncompress =>
    ⟨⟨74698472⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_finalVerify =>
    ⟨⟨333849714⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_millerLoop =>
    ⟨⟨254006273⟩, ⟨72⟩⟩
  | BuiltinFun.Bls12_381_mulMlResult =>
    ⟨⟨2174038⟩, ⟨72⟩⟩
  | BuiltinFun.ByteStringToInteger =>
    ⟨⟨1006041 + 43623 * argSize args 1 + 251 * (argSize args 1)^2⟩, ⟨argSize args 1⟩⟩
  | BuiltinFun.ChooseData =>
    ⟨⟨19537⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseList =>
    ⟨⟨175354⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseUnit =>
    ⟨⟨46417⟩, ⟨4⟩⟩
  | BuiltinFun.ConsByteString =>
    ⟨⟨221973 + 511 * argSize args 1⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.ConstrData =>
    ⟨⟨89141⟩, ⟨32⟩⟩
  | BuiltinFun.DecodeUtf8 =>
    ⟨⟨497525 + 14068 * argSize args 0⟩, ⟨4 + 2 * argSize args 0⟩⟩
  | BuiltinFun.DivideInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 196500 else 453240 + 220 * argSize args 0 * argSize args 1⟩, ⟨max 1 ((argSize args 0 - argSize args 1))⟩⟩
  | BuiltinFun.EncodeUtf8 =>
    ⟨⟨1000 + 28662 * argSize args 0⟩, ⟨4 + 2 * argSize args 0⟩⟩
  | BuiltinFun.EqualsByteString =>
    ⟨⟨if argSize args 0 == argSize args 1 then 216773 + 62 * argSize args 0 else 245000⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsData =>
    ⟨⟨1060367 + 12586 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsInteger =>
    ⟨⟨208512 + 421 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsString =>
    ⟨⟨if argSize args 0 == argSize args 1 then 1000 + 52998 * argSize args 0 else 187000⟩, ⟨1⟩⟩
  | BuiltinFun.FstPair =>
    ⟨⟨80436⟩, ⟨32⟩⟩
  | BuiltinFun.HeadList =>
    ⟨⟨43249⟩, ⟨32⟩⟩
  | BuiltinFun.IData =>
    ⟨⟨1000⟩, ⟨32⟩⟩
  | BuiltinFun.IfThenElse =>
    ⟨⟨80556⟩, ⟨1⟩⟩
  | BuiltinFun.IndexByteString =>
    ⟨⟨57667⟩, ⟨4⟩⟩
  | BuiltinFun.Keccak_256 =>
    ⟨⟨2261318 + 64571 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.LengthOfByteString =>
    ⟨⟨1000⟩, ⟨10⟩⟩
  | BuiltinFun.LessThanByteString =>
    ⟨⟨197145 + 156 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanEqualsByteString =>
    ⟨⟨197145 + 156 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanEqualsInteger =>
    ⟨⟨204924 + 473 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanInteger =>
    ⟨⟨208896 + 511 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.ListData =>
    ⟨⟨52467⟩, ⟨32⟩⟩
  | BuiltinFun.MapData =>
    ⟨⟨64832⟩, ⟨32⟩⟩
  | BuiltinFun.MkCons =>
    ⟨⟨65493⟩, ⟨32⟩⟩
  | BuiltinFun.MkNilData =>
    ⟨⟨22558⟩, ⟨32⟩⟩
  | BuiltinFun.MkNilPairData =>
    ⟨⟨16563⟩, ⟨32⟩⟩
  | BuiltinFun.MkPairData =>
    ⟨⟨76511⟩, ⟨32⟩⟩
  | BuiltinFun.ModInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 196500 else 453240 + 220 * argSize args 0 * argSize args 1⟩, ⟨max 1 (argSize args 0 - argSize args 1)⟩⟩
  | BuiltinFun.MultiplyInteger =>
    ⟨⟨69522 + 11687 * addedArgSize args⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.NullList =>
    ⟨⟨60091⟩, ⟨32⟩⟩
  | BuiltinFun.QuotientInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 196500 else 453240 + 220 * argSize args 0 * argSize args 1⟩, ⟨max 1 (argSize args 0 - argSize args 1)⟩⟩
  | BuiltinFun.RemainderInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 196500 else 453240 + 220 * argSize args 0 * argSize args 1⟩, ⟨max 1 (argSize args 0 - argSize args 1)⟩⟩
  | BuiltinFun.SerializeData =>
    ⟨⟨1159724 + 392670 * argSize args 0⟩, ⟨2 * argSize args 0⟩⟩
  | BuiltinFun.Sha2_256 =>
    ⟨⟨806990 + 30482 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Sha3_256 =>
    ⟨⟨1927926 + 82523 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.SliceByteString =>
    ⟨⟨265318⟩, ⟨4⟩⟩
  | BuiltinFun.SndPair =>
    ⟨⟨85931⟩, ⟨32⟩⟩
  | BuiltinFun.SubtractInteger =>
    ⟨⟨205665 + 812 * maxArgSize args⟩, ⟨1 + 1 * maxArgSize args⟩⟩
  | BuiltinFun.TailList =>
    ⟨⟨41182⟩, ⟨32⟩⟩
  | BuiltinFun.Trace =>
    ⟨⟨212342⟩, ⟨32⟩⟩
  | BuiltinFun.UnBData =>
    ⟨⟨31220⟩, ⟨32⟩⟩
  | BuiltinFun.UnConstrData =>
    ⟨⟨32696⟩, ⟨32⟩⟩
  | BuiltinFun.UnIData =>
    ⟨⟨43357⟩, ⟨32⟩⟩
  | BuiltinFun.UnListData =>
    ⟨⟨32247⟩, ⟨32⟩⟩
  | BuiltinFun.UnMapData =>
    ⟨⟨38314⟩, ⟨32⟩⟩
  | BuiltinFun.VerifyEcdsaSecp256k1Signature =>
    ⟨⟨35190005⟩, ⟨10⟩⟩
  | BuiltinFun.VerifyEd25519Signature =>
    ⟨⟨57996947 + 18975 * argSize args 2⟩, ⟨10⟩⟩
  | BuiltinFun.VerifySchnorrSecp256k1Signature =>
    ⟨⟨39121781 + 32260 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.AndByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.OrByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.XorByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.ComplementByteString =>
    ⟨⟨107878 + 680 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReadBit =>
    ⟨⟨95336⟩, ⟨1⟩⟩
  | BuiltinFun.WriteBits =>
    ⟨⟨281145 + 18848 * argSize args 1⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReplicateByte =>
    ⟨⟨180194 + 159 * argSize args 0⟩, ⟨1 + 1 * argSize args 0⟩⟩
  | BuiltinFun.ShiftByteString =>
    ⟨⟨158519 + 8942 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.RotateByteString =>
    ⟨⟨159378 + 8813 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.CountSetBits =>
    ⟨⟨107490 + 3298 * argSize args 0⟩, ⟨1⟩⟩
  | BuiltinFun.FindFirstSetBit =>
    ⟨⟨106057 + 655 * argSize args 0⟩, ⟨1⟩⟩
  | BuiltinFun.Ripemd_160 =>
    ⟨⟨1964219 + 24520 * argSize args 0⟩, ⟨3⟩⟩
  | BuiltinFun.ExpModInteger =>
    ⟨⟨987654321⟩, ⟨argSize args 2⟩⟩ -- TODO: exp_mod_cost formula (see Plutus source)
  | BuiltinFun.IntegerToByteString =>
    let memSize := match args[1]? with
      | some (CekValue.VCon (Const.Integer n)) => if n > 0 then n.toNat else argSize args 2
      | _                                       => argSize args 2
    ⟨⟨1293828 + 28716 * argSize args 2 + 63 * (argSize args 2)^2⟩, ⟨memSize⟩⟩
  | BuiltinFun.LengthOfArray =>
    ⟨⟨231883⟩, ⟨10⟩⟩
  | BuiltinFun.ListToArray =>
    ⟨⟨1000 + 24838 * argSize args 0⟩, ⟨7 + 1 * argSize args 0⟩⟩
  | BuiltinFun.IndexArray =>
    ⟨⟨232010⟩, ⟨32⟩⟩

def builtinCostsB (b : BuiltinFun) (args : List CekValue) : ExBudget :=
  match b with
  | BuiltinFun.AddInteger =>
    ⟨⟨100788 + 420 * maxArgSize args⟩, ⟨1 + 1 * maxArgSize args⟩⟩
  | BuiltinFun.AppendByteString =>
    ⟨⟨1000 + 173 * addedArgSize args⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.AppendString =>
    ⟨⟨1000 + 59957 * addedArgSize args⟩, ⟨4 + 1 * addedArgSize args⟩⟩
  | BuiltinFun.BData =>
    ⟨⟨11183⟩, ⟨32⟩⟩
  | BuiltinFun.Blake2b_224 =>
    ⟨⟨207616 + 8310 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Blake2b_256 =>
    ⟨⟨201305 + 8356 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Bls12_381_G1_add =>
    ⟨⟨962335⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_compress =>
    ⟨⟨2780678⟩, ⟨6⟩⟩
  | BuiltinFun.Bls12_381_G1_equal =>
    ⟨⟨442008⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G1_hashToGroup =>
    ⟨⟨52538055 + 3756 * argSize args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_neg =>
    ⟨⟨267929⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_scalarMul =>
    ⟨⟨76433006 + 8868 * argSize args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_uncompress =>
    ⟨⟨52948122⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_add =>
    ⟨⟨1995836⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_compress =>
    ⟨⟨3227919⟩, ⟨12⟩⟩
  | BuiltinFun.Bls12_381_G2_equal =>
    ⟨⟨901022⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G2_hashToGroup =>
    ⟨⟨166917843 + 4307 * argSize args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_neg =>
    ⟨⟨284546⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_scalarMul =>
    ⟨⟨158221314 + 26549 * argSize args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_uncompress =>
    ⟨⟨74698472⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_finalVerify =>
    ⟨⟨333849714⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_millerLoop =>
    ⟨⟨254006273⟩, ⟨72⟩⟩
  | BuiltinFun.Bls12_381_mulMlResult =>
    ⟨⟨2174038⟩, ⟨72⟩⟩
  | BuiltinFun.ByteStringToInteger =>
    ⟨⟨1006041 + 43623 * argSize args 1 + 251 * (argSize args 1)^2⟩, ⟨argSize args 1⟩⟩
  | BuiltinFun.ChooseData =>
    ⟨⟨94375⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseList =>
    ⟨⟨132994⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseUnit =>
    ⟨⟨61462⟩, ⟨4⟩⟩
  | BuiltinFun.ConsByteString =>
    ⟨⟨72010 + 178 * argSize args 1⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.ConstrData =>
    ⟨⟨22151⟩, ⟨32⟩⟩
  | BuiltinFun.DecodeUtf8 =>
    ⟨⟨91189 + 769 * argSize args 0⟩, ⟨4 + 2 * argSize args 0⟩⟩
  | BuiltinFun.DivideInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 85848 else 228465 + 122 * argSize args 0 * argSize args 1⟩, ⟨max 1 ((argSize args 0 - argSize args 1))⟩⟩
  | BuiltinFun.EncodeUtf8 =>
    ⟨⟨1000 + 42921 * argSize args 0⟩, ⟨4 + 2 * argSize args 0⟩⟩
  | BuiltinFun.EqualsByteString =>
    ⟨⟨if argSize args 0 == argSize args 1 then 29498 + 38 * argSize args 0 else 24548⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsData =>
    ⟨⟨898148 + 27279 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsInteger =>
    ⟨⟨51775 + 558 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsString =>
    ⟨⟨if argSize args 0 == argSize args 1 then 1000 + 60594 * argSize args 0 else 39184⟩, ⟨1⟩⟩
  | BuiltinFun.FstPair =>
    ⟨⟨141895⟩, ⟨32⟩⟩
  | BuiltinFun.HeadList =>
    ⟨⟨83150⟩, ⟨32⟩⟩
  | BuiltinFun.IData =>
    ⟨⟨15299⟩, ⟨32⟩⟩
  | BuiltinFun.IfThenElse =>
    ⟨⟨76049⟩, ⟨1⟩⟩
  | BuiltinFun.IndexByteString =>
    ⟨⟨13169⟩, ⟨4⟩⟩
  | BuiltinFun.IntegerToByteString =>
    -- memory: if arg 1 is a concrete positive integer, use it directly
    let memSize := match args[1]? with
      | some (CekValue.VCon (Const.Integer n)) => if n > 0 then n.toNat else argSize args 2
      | _                                       => argSize args 2
    ⟨⟨1293828 + 28716 * argSize args 2 + 63 * (argSize args 2)^2⟩, ⟨memSize⟩⟩
  | BuiltinFun.Keccak_256 =>
    ⟨⟨2261318 + 64571 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.LengthOfByteString =>
    ⟨⟨22100⟩, ⟨10⟩⟩
  | BuiltinFun.LessThanByteString =>
    ⟨⟨28999 + 74 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanEqualsByteString =>
    ⟨⟨28999 + 74 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanEqualsInteger =>
    ⟨⟨43285 + 552 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanInteger =>
    ⟨⟨44749 + 541 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.ListData =>
    ⟨⟨33852⟩, ⟨32⟩⟩
  | BuiltinFun.MapData =>
    ⟨⟨68246⟩, ⟨32⟩⟩
  | BuiltinFun.MkCons =>
    ⟨⟨72362⟩, ⟨32⟩⟩
  | BuiltinFun.MkNilData =>
    ⟨⟨7243⟩, ⟨32⟩⟩
  | BuiltinFun.MkNilPairData =>
    ⟨⟨7391⟩, ⟨32⟩⟩
  | BuiltinFun.MkPairData =>
    ⟨⟨11546⟩, ⟨32⟩⟩
  | BuiltinFun.ModInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 85848 else 228465 + 122 * argSize args 0 * argSize args 1⟩, ⟨max 1 ((argSize args 0 - argSize args 1))⟩⟩
  | BuiltinFun.MultiplyInteger =>
    ⟨⟨90434 + 519 * argSize args 0 * argSize args 1⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.NullList =>
    ⟨⟨74433⟩, ⟨32⟩⟩
  | BuiltinFun.QuotientInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 85848 else 228465 + 122 * argSize args 0 * argSize args 1⟩, ⟨max 1 ((argSize args 0 - argSize args 1))⟩⟩
  | BuiltinFun.RemainderInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 85848 else 228465 + 122 * argSize args 0 * argSize args 1⟩, ⟨max 1 ((argSize args 0 - argSize args 1))⟩⟩
  | BuiltinFun.SerializeData =>
    ⟨⟨955506 + 213312 * argSize args 0⟩, ⟨2 * argSize args 0⟩⟩
  | BuiltinFun.Sha2_256 =>
    ⟨⟨270652 + 22588 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Sha3_256 =>
    ⟨⟨1457325 + 64566 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.SliceByteString =>
    ⟨⟨20467 + 1 * argSize args 2⟩, ⟨4⟩⟩
  | BuiltinFun.SndPair =>
    ⟨⟨141992⟩, ⟨32⟩⟩
  | BuiltinFun.SubtractInteger =>
    ⟨⟨100788 + 420 * maxArgSize args⟩, ⟨1 + 1 * maxArgSize args⟩⟩
  | BuiltinFun.TailList =>
    ⟨⟨81663⟩, ⟨32⟩⟩
  | BuiltinFun.Trace =>
    ⟨⟨59498⟩, ⟨32⟩⟩
  | BuiltinFun.UnBData =>
    ⟨⟨20142⟩, ⟨32⟩⟩
  | BuiltinFun.UnConstrData =>
    ⟨⟨24588⟩, ⟨32⟩⟩
  | BuiltinFun.UnIData =>
    ⟨⟨20744⟩, ⟨32⟩⟩
  | BuiltinFun.UnListData =>
    ⟨⟨25933⟩, ⟨32⟩⟩
  | BuiltinFun.UnMapData =>
    ⟨⟨24623⟩, ⟨32⟩⟩
  | BuiltinFun.VerifyEcdsaSecp256k1Signature =>
    ⟨⟨43053543⟩, ⟨10⟩⟩
  | BuiltinFun.VerifyEd25519Signature =>
    ⟨⟨53384111 + 14333 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.VerifySchnorrSecp256k1Signature =>
    ⟨⟨43574283 + 26308 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.AndByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.OrByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.XorByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.ComplementByteString =>
    ⟨⟨107878 + 680 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReadBit =>
    ⟨⟨95336⟩, ⟨1⟩⟩
  | BuiltinFun.WriteBits =>
    ⟨⟨281145 + 18848 * argSize args 1⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReplicateByte =>
    ⟨⟨180194 + 159 * argSize args 0⟩, ⟨1 + 1 * argSize args 0⟩⟩
  | BuiltinFun.ShiftByteString =>
    ⟨⟨158519 + 8942 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.RotateByteString =>
    ⟨⟨159378 + 8813 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.CountSetBits =>
    ⟨⟨107490 + 3298 * argSize args 0⟩, ⟨1⟩⟩
  | BuiltinFun.FindFirstSetBit =>
    ⟨⟨106057 + 655 * argSize args 0⟩, ⟨1⟩⟩
  | BuiltinFun.Ripemd_160 =>
    ⟨⟨1964219 + 24520 * argSize args 0⟩, ⟨3⟩⟩
  | BuiltinFun.ExpModInteger =>
    ⟨⟨100000000000⟩, ⟨argSize args 2⟩⟩ -- TODO: exp_mod_cost formula (see Plutus source)
  | BuiltinFun.LengthOfArray =>
    ⟨⟨231883⟩, ⟨10⟩⟩
  | BuiltinFun.ListToArray =>
    ⟨⟨1000 + 24838 * argSize args 0⟩, ⟨7 + 1 * argSize args 0⟩⟩
  | BuiltinFun.IndexArray =>
    ⟨⟨232010⟩, ⟨32⟩⟩


def builtinCostsC (b : BuiltinFun) (args : List CekValue) : ExBudget :=
  match b with
  | BuiltinFun.AddInteger =>
    ⟨⟨100788 + 420 * maxArgSize args⟩, ⟨1 + 1 * maxArgSize args⟩⟩
  | BuiltinFun.AppendByteString =>
    ⟨⟨1000 + 173 * addedArgSize args⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.AppendString =>
    ⟨⟨1000 + 59957 * addedArgSize args⟩, ⟨4 + 1 * addedArgSize args⟩⟩
  | BuiltinFun.BData =>
    ⟨⟨11183⟩, ⟨32⟩⟩
  | BuiltinFun.Blake2b_224 =>
    ⟨⟨207616 + 8310 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Blake2b_256 =>
    ⟨⟨201305 + 8356 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Bls12_381_G1_add =>
    ⟨⟨962335⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_compress =>
    ⟨⟨2780678⟩, ⟨6⟩⟩
  | BuiltinFun.Bls12_381_G1_equal =>
    ⟨⟨442008⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G1_hashToGroup =>
    ⟨⟨52538055 + 3756 * argSize args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_neg =>
    ⟨⟨267929⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_scalarMul =>
    ⟨⟨76433006 + 8868 * argSize args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_uncompress =>
    ⟨⟨52948122⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_add =>
    ⟨⟨1995836⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_compress =>
    ⟨⟨3227919⟩, ⟨12⟩⟩
  | BuiltinFun.Bls12_381_G2_equal =>
    ⟨⟨901022⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G2_hashToGroup =>
    ⟨⟨166917843 + 4307 * argSize args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_neg =>
    ⟨⟨284546⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_scalarMul =>
    ⟨⟨158221314 + 26549 * argSize args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_uncompress =>
    ⟨⟨74698472⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_finalVerify =>
    ⟨⟨333849714⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_millerLoop =>
    ⟨⟨254006273⟩, ⟨72⟩⟩
  | BuiltinFun.Bls12_381_mulMlResult =>
    ⟨⟨2174038⟩, ⟨72⟩⟩
  | BuiltinFun.ByteStringToInteger =>
    ⟨⟨1006041 + 43623 * argSize args 1 + 251 * (argSize args 1)^2⟩, ⟨argSize args 1⟩⟩
  | BuiltinFun.ChooseData =>
    ⟨⟨94375⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseList =>
    ⟨⟨132994⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseUnit =>
    ⟨⟨61462⟩, ⟨4⟩⟩
  | BuiltinFun.ConsByteString =>
    ⟨⟨72010 + 178 * argSize args 1⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.ConstrData =>
    ⟨⟨22151⟩, ⟨32⟩⟩
  | BuiltinFun.DecodeUtf8 =>
    ⟨⟨91189 + 769 * argSize args 0⟩, ⟨4 + 2 * argSize args 0⟩⟩
  | BuiltinFun.DivideInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 85848 else Int.toNat (max 85848 (123203 + 1716 * ↑(argSize args 0) + 7305 * ↑(argSize args 1) + 57 * ↑(argSize args 0)^2 + 549 * ↑(argSize args 0) * ↑(argSize args 1) - 900 * ↑(argSize args 1)^2))⟩, ⟨max 1 ((argSize args 0 - argSize args 1))⟩⟩
  | BuiltinFun.EncodeUtf8 =>
    ⟨⟨1000 + 42921 * argSize args 0⟩, ⟨4 + 2 * argSize args 0⟩⟩
  | BuiltinFun.EqualsByteString =>
    ⟨⟨if argSize args 0 == argSize args 1 then 29498 + 38 * argSize args 0 else 24548⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsData =>
    ⟨⟨898148 + 27279 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsInteger =>
    ⟨⟨51775 + 558 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.EqualsString =>
    ⟨⟨if argSize args 0 == argSize args 1 then 1000 + 60594 * argSize args 0 else 39184⟩, ⟨1⟩⟩
  | BuiltinFun.FstPair =>
    ⟨⟨141895⟩, ⟨32⟩⟩
  | BuiltinFun.HeadList =>
    ⟨⟨83150⟩, ⟨32⟩⟩
  | BuiltinFun.IData =>
    ⟨⟨15299⟩, ⟨32⟩⟩
  | BuiltinFun.IfThenElse =>
    ⟨⟨76049⟩, ⟨1⟩⟩
  | BuiltinFun.IndexByteString =>
    ⟨⟨13169⟩, ⟨4⟩⟩
  | BuiltinFun.IntegerToByteString =>
    -- memory: if arg 1 is a concrete positive integer, use it directly
    let memSize := match args[1]? with
      | some (CekValue.VCon (Const.Integer n)) => if n > 0 then n.toNat else argSize args 2
      | _                                       => argSize args 2
    ⟨⟨1293828 + 28716 * argSize args 2 + 63 * (argSize args 2)^2⟩, ⟨memSize⟩⟩
  | BuiltinFun.Keccak_256 =>
    ⟨⟨2261318 + 64571 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.LengthOfByteString =>
    ⟨⟨22100⟩, ⟨10⟩⟩
  | BuiltinFun.LessThanByteString =>
    ⟨⟨28999 + 74 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanEqualsByteString =>
    ⟨⟨28999 + 74 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanEqualsInteger =>
    ⟨⟨43285 + 552 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.LessThanInteger =>
    ⟨⟨44749 + 541 * minArgSize args⟩, ⟨1⟩⟩
  | BuiltinFun.ListData =>
    ⟨⟨33852⟩, ⟨32⟩⟩
  | BuiltinFun.MapData =>
    ⟨⟨68246⟩, ⟨32⟩⟩
  | BuiltinFun.MkCons =>
    ⟨⟨72362⟩, ⟨32⟩⟩
  | BuiltinFun.MkNilData =>
    ⟨⟨7243⟩, ⟨32⟩⟩
  | BuiltinFun.MkNilPairData =>
    ⟨⟨7391⟩, ⟨32⟩⟩
  | BuiltinFun.MkPairData =>
    ⟨⟨11546⟩, ⟨32⟩⟩
  | BuiltinFun.ModInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 85848 else Int.toNat (max 85848 (123203 + 1716 * ↑(argSize args 0) + 7305 * ↑(argSize args 1) + 57 * ↑(argSize args 0)^2 + 549 * ↑(argSize args 0) * ↑(argSize args 1) - 900 * ↑(argSize args 1)^2))⟩, ⟨argSize args 1⟩⟩
  | BuiltinFun.MultiplyInteger =>
    ⟨⟨90434 + 519 * argSize args 0 * argSize args 1⟩, ⟨addedArgSize args⟩⟩
  | BuiltinFun.NullList =>
    ⟨⟨74433⟩, ⟨32⟩⟩
  | BuiltinFun.QuotientInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 85848 else Int.toNat (max 85848 (123203 + 1716 * ↑(argSize args 0) + 7305 * ↑(argSize args 1) + 57 * ↑(argSize args 0)^2 + 549 * ↑(argSize args 0) * ↑(argSize args 1) - 900 * ↑(argSize args 1)^2))⟩, ⟨max 1 ((argSize args 0 - argSize args 1))⟩⟩
  | BuiltinFun.RemainderInteger =>
    ⟨⟨if argSize args 1 > argSize args 0 then 85848 else Int.toNat (max 85848 (123203 + 1716 * ↑(argSize args 0) + 7305 * ↑(argSize args 1) + 57 * ↑(argSize args 0)^2 + 549 * ↑(argSize args 0) * ↑(argSize args 1) - 900 * ↑(argSize args 1)^2))⟩, ⟨argSize args 1⟩⟩
  | BuiltinFun.SerializeData =>
    ⟨⟨955506 + 213312 * argSize args 0⟩, ⟨2 * argSize args 0⟩⟩
  | BuiltinFun.Sha2_256 =>
    ⟨⟨270652 + 22588 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.Sha3_256 =>
    ⟨⟨1457325 + 64566 * argSize args 0⟩, ⟨4⟩⟩
  | BuiltinFun.SliceByteString =>
    ⟨⟨20467 + 1 * argSize args 2⟩, ⟨4⟩⟩
  | BuiltinFun.SndPair =>
    ⟨⟨141992⟩, ⟨32⟩⟩
  | BuiltinFun.SubtractInteger =>
    ⟨⟨100788 + 420 * maxArgSize args⟩, ⟨1 + 1 * maxArgSize args⟩⟩
  | BuiltinFun.TailList =>
    ⟨⟨81663⟩, ⟨32⟩⟩
  | BuiltinFun.Trace =>
    ⟨⟨59498⟩, ⟨32⟩⟩
  | BuiltinFun.UnBData =>
    ⟨⟨20142⟩, ⟨32⟩⟩
  | BuiltinFun.UnConstrData =>
    ⟨⟨24588⟩, ⟨32⟩⟩
  | BuiltinFun.UnIData =>
    ⟨⟨20744⟩, ⟨32⟩⟩
  | BuiltinFun.UnListData =>
    ⟨⟨25933⟩, ⟨32⟩⟩
  | BuiltinFun.UnMapData =>
    ⟨⟨24623⟩, ⟨32⟩⟩
  | BuiltinFun.VerifyEcdsaSecp256k1Signature =>
    ⟨⟨43053543⟩, ⟨10⟩⟩
  | BuiltinFun.VerifyEd25519Signature =>
    ⟨⟨53384111 + 14333 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.VerifySchnorrSecp256k1Signature =>
    ⟨⟨43574283 + 26308 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.AndByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.OrByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.XorByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 2⟩, ⟨max (argSize args 1) (argSize args 2)⟩⟩
  | BuiltinFun.ComplementByteString =>
    ⟨⟨107878 + 680 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReadBit =>
    ⟨⟨95336⟩, ⟨1⟩⟩
  | BuiltinFun.WriteBits =>
    ⟨⟨281145 + 18848 * argSize args 1⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReplicateByte =>
    ⟨⟨180194 + 159 * argSize args 0⟩, ⟨1 + 1 * argSize args 0⟩⟩
  | BuiltinFun.ShiftByteString =>
    ⟨⟨158519 + 8942 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.RotateByteString =>
    ⟨⟨159378 + 8813 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.CountSetBits =>
    ⟨⟨107490 + 3298 * argSize args 0⟩, ⟨1⟩⟩
  | BuiltinFun.FindFirstSetBit =>
    ⟨⟨106057 + 655 * argSize args 0⟩, ⟨1⟩⟩
  | BuiltinFun.Ripemd_160 =>
    ⟨⟨1964219 + 24520 * argSize args 0⟩, ⟨3⟩⟩
  | BuiltinFun.ExpModInteger =>
    ⟨⟨100000000000⟩, ⟨argSize args 2⟩⟩ -- TODO: exp_mod_cost formula (see Plutus source)
  | BuiltinFun.LengthOfArray =>
    ⟨⟨231883⟩, ⟨10⟩⟩
  | BuiltinFun.ListToArray =>
    ⟨⟨1000 + 24838 * argSize args 0⟩, ⟨7 + 1 * argSize args 0⟩⟩
  | BuiltinFun.IndexArray =>
    ⟨⟨232010⟩, ⟨32⟩⟩

def builtinCostSelected (semVar: BuiltinSemanticsVariant) (b : BuiltinFun) (args : List CekValue) : ExBudget :=
  match semVar with
  | .defaultFunSemanticsVariantA => builtinCostsA b args
  | .defaultFunSemanticsVariantB => builtinCostsB b args
  | .defaultFunSemanticsVariantC => builtinCostsC b args

end PlutusCore.UPLC.CostModels
