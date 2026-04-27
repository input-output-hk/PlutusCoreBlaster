/- Cost model for UPLC CEK Machine evaluation -/
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
  }

-- Helpers

-- TODO: Either fix something so we can add the real implementation or decide if we're ok with that
/-- Blaster friendly Integer size-/
def integerSize (i : Integer) : Nat :=
  let n := i.natAbs
  if n == 0 then 1
  else n.log2 / 64 + 1


/-- Calculate the size of a bytestring in 8-byte words (minimum 1).
    Matches Haskell's `((n-1) `quot` 8) + 1` — empty bytestring has size 1. -/
def byteStringSize (bs : ByteString) : Nat :=
  let n := bs.data.length
  (n - 1) / 8 + 1  -- saturating subtraction: n=0 gives (0/8)+1 = 1


mutual
  def dataSize (d : Data) : Nat :=
    match d with
    | Data.Constr _ ds => 4 + dataSizeList ds
    | Data.Map kvs => 4 + dataSizeMap kvs
    | Data.List ds => 4 + dataSizeList ds
    | Data.I i => 4 + integerSize i
    | Data.B bs => 4 + byteStringSize bs

  def dataSizeList : List Data → Nat
    | [] => 0
    | d :: ds => dataSize d + dataSizeList ds

  def dataSizeMap : List (Data × Data) → Nat
    | [] => 0
    | (k, v) :: kvs => dataSize k + dataSize v + dataSizeMap kvs
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
  | Const.Pair (c1, c2) => constSize c1 + constSize c2
  | Const.PairData (d1, d2) => dataSize d1 + dataSize d2
  | Const.Data d => dataSize d
  | Const.Bls12_381_G1_element _ => 48
  | Const.Bls12_381_G2_element _ => 96
  | Const.Bls12_381_MlResult _ => 576

def cekValueSize (v : CekValue) : Nat :=
  match v with
    | CekValue.VCon c => constSize c
    | _ => 1

def argSize (args : List CekValue) (i : Nat) : Nat :=
  if h : i < args.length then cekValueSize (args.get ⟨i, h⟩) else 1 -- 1?

/-- Length of the list constant at position i in the CEK args. -/
def argListLen (args : List CekValue) (i : Nat) : Nat :=
  if h : i < args.length then
    match args.get ⟨i, h⟩ with
    | .VCon (.ConstList cs) => cs.length
    | _ => 0
  else 0

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
    -- Source: bls12_381_G1_hashToGroup msg dst; CEK args = [dst, msg].
    -- CPU: linear_in_x → slope * size(msg) = argSize args 1.
    ⟨⟨52538055 + 3756 * argSize args 1⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_neg =>
    ⟨⟨267929⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_scalarMul =>
    -- Source: bls12_381_G1_scalarMul z x (z=scalar, x=point); CEK args = [point, scalar].
    -- CPU: linear_in_x → slope * size(scalar) = argSize args 1.
    ⟨⟨76433006 + 8868 * argSize args 1⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_uncompress =>
    ⟨⟨52948122⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_add =>
    ⟨⟨1995836⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_compress =>
    ⟨⟨3227919⟩, ⟨12⟩⟩
  | BuiltinFun.Bls12_381_G2_equal =>
    ⟨⟨901022⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G2_hashToGroup =>
    -- Source: bls12_381_G2_hashToGroup msg dst; CEK args = [dst, msg].
    -- CPU: linear_in_x → slope * size(msg) = argSize args 1.
    ⟨⟨166917843 + 4307 * argSize args 1⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_neg =>
    ⟨⟨284546⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_scalarMul =>
    -- Source: bls12_381_G2_scalarMul z x (z=scalar, x=point); CEK args = [point, scalar].
    -- CPU: linear_in_x → slope * size(scalar) = argSize args 1.
    ⟨⟨158221314 + 26549 * argSize args 1⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_uncompress =>
    ⟨⟨74698472⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_finalVerify =>
    ⟨⟨333849714⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G1_multiScalarMul =>
    ⟨⟨321837444 + 25087669 * argListLen args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_multiScalarMul =>
    ⟨⟨617887431 + 67302824 * argListLen args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_millerLoop =>
    ⟨⟨254006273⟩, ⟨72⟩⟩
  | BuiltinFun.Bls12_381_mulMlResult =>
    ⟨⟨2174038⟩, ⟨72⟩⟩
  | BuiltinFun.ByteStringToInteger =>
    -- Source: byteStringToInteger endian bs; CEK args = [bs, endian].
    -- CPU: quadratic_in_y → c0 + c1*size(bs) + c2*size(bs)^2; size(bs) = argSize args 0.
    -- Memory: linear_in_y (intercept 0, slope 1) → size(bs) = argSize args 0.
    ⟨⟨1006041 + 43623 * argSize args 0 + 251 * (argSize args 0)^2⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ChooseData =>
    ⟨⟨19537⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseList =>
    ⟨⟨175354⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseUnit =>
    ⟨⟨46417⟩, ⟨4⟩⟩
  | BuiltinFun.ConsByteString =>
    -- Source: consByteString x bs; CEK args = [bs, x].
    -- CPU: linear_in_y → slope * size(bs) = argSize args 0.
    -- Memory: added_sizes (size(x) + size(bs)) = addedArgSize.
    ⟨⟨221973 + 511 * argSize args 0⟩, ⟨addedArgSize args⟩⟩
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
    -- Source: verifyEd25519Signature pk msg sig; CEK args = [sig, msg, pk].
    -- Model: linear_in_y → slope * size(msg) = argSize args 1.
    ⟨⟨57996947 + 18975 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.VerifySchnorrSecp256k1Signature =>
    -- Source: verifySchnorrSecp256k1Signature pk msg sig; CEK args = [sig, msg, pk].
    -- Model: linear_in_y → slope * size(msg) = argSize args 1.
    ⟨⟨39121781 + 32260 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.AndByteString =>
    -- Source: andByteString endian op1 op2; CEK args = [op2, op1, endian].
    -- CPU: linear_in_y_and_z = slope1*size(op1) + slope2*size(op2)
    --                       = 726*argSize args 1 + 719*argSize args 0.
    -- Memory: linear_in_max_yz (intercept 0, slope 1) = max(size(op1), size(op2)).
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.OrByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.XorByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.ComplementByteString =>
    ⟨⟨107878 + 680 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReadBit =>
    ⟨⟨95336⟩, ⟨1⟩⟩
  | BuiltinFun.WriteBits =>
    -- Source: writeBits s idxs flag; CEK args = [flag, idxs, s].
    -- CPU: linear_in_y → slope * size(idxs) = argSize args 1.
    -- Memory: linear_in_x (slope 1) → size(s) = argSize args 2.
    ⟨⟨281145 + 18848 * argSize args 1⟩, ⟨argSize args 2⟩⟩
  | BuiltinFun.ReplicateByte =>
    -- Source: replicateByte n byte; CEK args = [byte, n].
    -- x = NumBytesCostedAsNumWords(n) where n = args[1]: 0 for n ≤ 0, else (n-1)/8+1.
    let x := match (args[1]? : Option CekValue) with
      | some (CekValue.VCon (Const.Integer n)) =>
          if n ≤ 0 then 0 else (n.toNat - 1) / 8 + 1
      | _ => 0
    ⟨⟨180194 + 159 * x⟩, ⟨1 + 1 * x⟩⟩
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
    -- Source: expModInteger b e m; CEK args = [m, e, b].
    -- Model: exp_mod_cost; aa=size(b)=args[2], ee=size(e)=args[1], mm=size(m)=args[0].
    -- cost0 = c00 + c11*ee*mm + c12*ee*mm^2; if aa > mm: cost0 + cost0/2 (50% penalty).
    -- Memory: linear_in_z (intercept 0, slope 1) = size(m) = argSize args 0.
    let mm := argSize args 0
    let ee := argSize args 1
    let aa := argSize args 2
    let cost0 := 607153 + 231697 * ee * mm + 53144 * ee * mm^2
    ⟨⟨if aa > mm then cost0 + cost0 / 2 else cost0⟩, ⟨mm⟩⟩
  | BuiltinFun.DropList =>
    -- Source: dropList n xs; after force, CEK args = [xs, n].
    -- Model: linear_in_x where x = IntegerCostedLiterally(n) = |n|; n = args[1].
    let x := match (args[1]? : Option CekValue) with
      | some (CekValue.VCon (Const.Integer n)) => n.natAbs
      | _ => 0
    ⟨⟨116711 + 1957 * x⟩, ⟨4⟩⟩
  | BuiltinFun.IntegerToByteString =>
    -- Source: integerToByteString endian width n; CEK args = [n, width, endian].
    -- CPU: quadratic_in_z = c0 + c1*size(n) + c2*size(n)^2; size(n) = argSize args 0.
    -- Memory: literal_in_y_or_linear_in_z;
    --   if width > 0: NumBytesCostedAsNumWords(width) = (width-1)/8+1 (width at args[1]),
    --   else (width=0, unbounded): linear_in_z (slope 1) = size(n) = argSize args 0.
    let memSize := match args[1]? with
      | some (CekValue.VCon (Const.Integer n)) =>
          if n > 0 then (n.toNat - 1) / 8 + 1 else argSize args 0
      | _ => argSize args 0
    ⟨⟨1293828 + 28716 * argSize args 0 + 63 * (argSize args 0)^2⟩, ⟨memSize⟩⟩

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
    -- Source: bls12_381_G1_hashToGroup msg dst; CEK args = [dst, msg].
    -- CPU: linear_in_x → slope * size(msg) = argSize args 1.
    ⟨⟨52538055 + 3756 * argSize args 1⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_neg =>
    ⟨⟨267929⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_scalarMul =>
    -- Source: bls12_381_G1_scalarMul z x (z=scalar, x=point); CEK args = [point, scalar].
    -- CPU: linear_in_x → slope * size(scalar) = argSize args 1.
    ⟨⟨76433006 + 8868 * argSize args 1⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_uncompress =>
    ⟨⟨52948122⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_add =>
    ⟨⟨1995836⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_compress =>
    ⟨⟨3227919⟩, ⟨12⟩⟩
  | BuiltinFun.Bls12_381_G2_equal =>
    ⟨⟨901022⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G2_hashToGroup =>
    -- Source: bls12_381_G2_hashToGroup msg dst; CEK args = [dst, msg].
    -- CPU: linear_in_x → slope * size(msg) = argSize args 1.
    ⟨⟨166917843 + 4307 * argSize args 1⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_neg =>
    ⟨⟨284546⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_scalarMul =>
    -- Source: bls12_381_G2_scalarMul z x (z=scalar, x=point); CEK args = [point, scalar].
    -- CPU: linear_in_x → slope * size(scalar) = argSize args 1.
    ⟨⟨158221314 + 26549 * argSize args 1⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_uncompress =>
    ⟨⟨74698472⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G1_multiScalarMul =>
    ⟨⟨321837444 + 25087669 * argListLen args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_multiScalarMul =>
    ⟨⟨617887431 + 67302824 * argListLen args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_finalVerify =>
    ⟨⟨333849714⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_millerLoop =>
    ⟨⟨254006273⟩, ⟨72⟩⟩
  | BuiltinFun.Bls12_381_mulMlResult =>
    ⟨⟨2174038⟩, ⟨72⟩⟩
  | BuiltinFun.ByteStringToInteger =>
    -- Source: byteStringToInteger endian bs; CEK args = [bs, endian].
    -- CPU: quadratic_in_y → c0 + c1*size(bs) + c2*size(bs)^2; size(bs) = argSize args 0.
    -- Memory: linear_in_y (intercept 0, slope 1) → size(bs) = argSize args 0.
    ⟨⟨1006041 + 43623 * argSize args 0 + 251 * (argSize args 0)^2⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ChooseData =>
    ⟨⟨94375⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseList =>
    ⟨⟨132994⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseUnit =>
    ⟨⟨61462⟩, ⟨4⟩⟩
  | BuiltinFun.ConsByteString =>
    -- Source: consByteString x bs; CEK args = [bs, x].
    -- CPU: linear_in_y → slope * size(bs) = argSize args 0.
    -- Memory: added_sizes (size(x) + size(bs)) = addedArgSize.
    ⟨⟨72010 + 178 * argSize args 0⟩, ⟨addedArgSize args⟩⟩
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
    -- Source: integerToByteString endian width n; CEK args = [n, width, endian].
    -- CPU: quadratic_in_z = c0 + c1*size(n) + c2*size(n)^2; size(n) = argSize args 0.
    -- Memory: literal_in_y_or_linear_in_z;
    --   if width > 0: NumBytesCostedAsNumWords(width) = (width-1)/8+1 (width at args[1]),
    --   else (width=0, unbounded): linear_in_z (slope 1) = size(n) = argSize args 0.
    let memSize := match args[1]? with
      | some (CekValue.VCon (Const.Integer n)) =>
          if n > 0 then (n.toNat - 1) / 8 + 1 else argSize args 0
      | _ => argSize args 0
    ⟨⟨1293828 + 28716 * argSize args 0 + 63 * (argSize args 0)^2⟩, ⟨memSize⟩⟩
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
    -- Source: sliceByteString s k bs; CEK args = [bs, k, s].
    -- CPU: linear_in_z → slope * size(bs) = argSize args 0.
    -- Memory: linear_in_z (intercept 4, slope 0) → constant 4.
    ⟨⟨20467 + 1 * argSize args 0⟩, ⟨4⟩⟩
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
    -- Source: verifyEd25519Signature pk msg sig; CEK args = [sig, msg, pk].
    -- Model: linear_in_y → slope * size(msg) = argSize args 1.
    ⟨⟨53384111 + 14333 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.VerifySchnorrSecp256k1Signature =>
    -- Source: verifySchnorrSecp256k1Signature pk msg sig; CEK args = [sig, msg, pk].
    -- Model: linear_in_y → slope * size(msg) = argSize args 1.
    ⟨⟨43574283 + 26308 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.AndByteString =>
    -- Source: andByteString endian op1 op2; CEK args = [op2, op1, endian].
    -- CPU: linear_in_y_and_z = slope1*size(op1) + slope2*size(op2).
    -- Memory: linear_in_max_yz (intercept 0, slope 1) = max(size(op1), size(op2)).
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.OrByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.XorByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.ComplementByteString =>
    ⟨⟨107878 + 680 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReadBit =>
    ⟨⟨95336⟩, ⟨1⟩⟩
  | BuiltinFun.WriteBits =>
    -- Source: writeBits s idxs flag; CEK args = [flag, idxs, s].
    -- CPU: linear_in_y → slope * size(idxs) = argSize args 1.
    -- Memory: linear_in_x (slope 1) → size(s) = argSize args 2.
    ⟨⟨281145 + 18848 * argSize args 1⟩, ⟨argSize args 2⟩⟩
  | BuiltinFun.ReplicateByte =>
    -- Source: replicateByte n byte; CEK args = [byte, n].
    -- x = NumBytesCostedAsNumWords(n) where n = args[1]: 0 for n ≤ 0, else (n-1)/8+1.
    let x := match (args[1]? : Option CekValue) with
      | some (CekValue.VCon (Const.Integer n)) =>
          if n ≤ 0 then 0 else (n.toNat - 1) / 8 + 1
      | _ => 0
    ⟨⟨180194 + 159 * x⟩, ⟨1 + 1 * x⟩⟩
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
    -- Source: expModInteger b e m; CEK args = [m, e, b].
    -- CPU: exp_mod_cost; aa=size(b)=args[2], ee=size(e)=args[1], mm=size(m)=args[0].
    -- cost0 = c00 + c11*ee*mm + c12*ee*mm^2; if aa > mm: cost0 + cost0/2.
    -- Memory: linear_in_z (intercept 0, slope 1) = size(m) = argSize args 0.
    let mm := argSize args 0
    let ee := argSize args 1
    let aa := argSize args 2
    let cost0 := 607153 + 231697 * ee * mm + 53144 * ee * mm^2
    ⟨⟨if aa > mm then cost0 + cost0 / 2 else cost0⟩, ⟨mm⟩⟩
  | BuiltinFun.DropList =>
    -- Source: dropList n xs; after force, CEK args = [xs, n].
    -- Model: linear_in_x where x = IntegerCostedLiterally(n) = |n|; n = args[1].
    let x := match (args[1]? : Option CekValue) with
      | some (CekValue.VCon (Const.Integer n)) => n.natAbs
      | _ => 0
    ⟨⟨116711 + 1957 * x⟩, ⟨4⟩⟩


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
    -- Source: bls12_381_G1_hashToGroup msg dst; CEK args = [dst, msg].
    -- CPU: linear_in_x → slope * size(msg) = argSize args 1.
    ⟨⟨52538055 + 3756 * argSize args 1⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_neg =>
    ⟨⟨267929⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_scalarMul =>
    -- Source: bls12_381_G1_scalarMul z x (z=scalar, x=point); CEK args = [point, scalar].
    -- CPU: linear_in_x → slope * size(scalar) = argSize args 1.
    ⟨⟨76433006 + 8868 * argSize args 1⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G1_uncompress =>
    ⟨⟨52948122⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_add =>
    ⟨⟨1995836⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_compress =>
    ⟨⟨3227919⟩, ⟨12⟩⟩
  | BuiltinFun.Bls12_381_G2_equal =>
    ⟨⟨901022⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_G2_hashToGroup =>
    -- Source: bls12_381_G2_hashToGroup msg dst; CEK args = [dst, msg].
    -- CPU: linear_in_x → slope * size(msg) = argSize args 1.
    ⟨⟨166917843 + 4307 * argSize args 1⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_neg =>
    ⟨⟨284546⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_scalarMul =>
    -- Source: bls12_381_G2_scalarMul z x (z=scalar, x=point); CEK args = [point, scalar].
    -- CPU: linear_in_x → slope * size(scalar) = argSize args 1.
    ⟨⟨158221314 + 26549 * argSize args 1⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G2_uncompress =>
    ⟨⟨74698472⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_G1_multiScalarMul =>
    ⟨⟨321837444 + 25087669 * argListLen args 0⟩, ⟨18⟩⟩
  | BuiltinFun.Bls12_381_G2_multiScalarMul =>
    ⟨⟨617887431 + 67302824 * argListLen args 0⟩, ⟨36⟩⟩
  | BuiltinFun.Bls12_381_finalVerify =>
    ⟨⟨333849714⟩, ⟨1⟩⟩
  | BuiltinFun.Bls12_381_millerLoop =>
    ⟨⟨254006273⟩, ⟨72⟩⟩
  | BuiltinFun.Bls12_381_mulMlResult =>
    ⟨⟨2174038⟩, ⟨72⟩⟩
  | BuiltinFun.ByteStringToInteger =>
    -- Source: byteStringToInteger endian bs; CEK args = [bs, endian].
    -- CPU: quadratic_in_y → c0 + c1*size(bs) + c2*size(bs)^2; size(bs) = argSize args 0.
    -- Memory: linear_in_y (intercept 0, slope 1) → size(bs) = argSize args 0.
    ⟨⟨1006041 + 43623 * argSize args 0 + 251 * (argSize args 0)^2⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ChooseData =>
    ⟨⟨94375⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseList =>
    ⟨⟨132994⟩, ⟨32⟩⟩
  | BuiltinFun.ChooseUnit =>
    ⟨⟨61462⟩, ⟨4⟩⟩
  | BuiltinFun.ConsByteString =>
    -- Source: consByteString x bs; CEK args = [bs, x].
    -- CPU: linear_in_y → slope * size(bs) = argSize args 0.
    -- Memory: added_sizes (size(x) + size(bs)) = addedArgSize.
    ⟨⟨72010 + 178 * argSize args 0⟩, ⟨addedArgSize args⟩⟩
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
    -- Source: integerToByteString endian width n; CEK args = [n, width, endian].
    -- CPU: quadratic_in_z = c0 + c1*size(n) + c2*size(n)^2; size(n) = argSize args 0.
    -- Memory: literal_in_y_or_linear_in_z;
    --   if width > 0: NumBytesCostedAsNumWords(width) = (width-1)/8+1 (width at args[1]),
    --   else (width=0, unbounded): linear_in_z (slope 1) = size(n) = argSize args 0.
    let memSize := match args[1]? with
      | some (CekValue.VCon (Const.Integer n)) =>
          if n > 0 then (n.toNat - 1) / 8 + 1 else argSize args 0
      | _ => argSize args 0
    ⟨⟨1293828 + 28716 * argSize args 0 + 63 * (argSize args 0)^2⟩, ⟨memSize⟩⟩
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
    -- Source: sliceByteString s k bs; CEK args = [bs, k, s].
    -- CPU: linear_in_z → slope * size(bs) = argSize args 0.
    -- Memory: linear_in_z (intercept 4, slope 0) → constant 4.
    ⟨⟨20467 + 1 * argSize args 0⟩, ⟨4⟩⟩
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
    -- Source: verifyEd25519Signature pk msg sig; CEK args = [sig, msg, pk].
    -- Model: linear_in_y → slope * size(msg) = argSize args 1.
    ⟨⟨53384111 + 14333 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.VerifySchnorrSecp256k1Signature =>
    -- Source: verifySchnorrSecp256k1Signature pk msg sig; CEK args = [sig, msg, pk].
    -- Model: linear_in_y → slope * size(msg) = argSize args 1.
    ⟨⟨43574283 + 26308 * argSize args 1⟩, ⟨10⟩⟩
  | BuiltinFun.AndByteString =>
    -- Source: andByteString endian op1 op2; CEK args = [op2, op1, endian].
    -- CPU: linear_in_y_and_z = slope1*size(op1) + slope2*size(op2).
    -- Memory: linear_in_max_yz (intercept 0, slope 1) = max(size(op1), size(op2)).
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.OrByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.XorByteString =>
    ⟨⟨100181 + 726 * argSize args 1 + 719 * argSize args 0⟩, ⟨max (argSize args 0) (argSize args 1)⟩⟩
  | BuiltinFun.ComplementByteString =>
    ⟨⟨107878 + 680 * argSize args 0⟩, ⟨argSize args 0⟩⟩
  | BuiltinFun.ReadBit =>
    ⟨⟨95336⟩, ⟨1⟩⟩
  | BuiltinFun.WriteBits =>
    -- Source: writeBits s idxs flag; CEK args = [flag, idxs, s].
    -- CPU: linear_in_y → slope * size(idxs) = argSize args 1.
    -- Memory: linear_in_x (slope 1) → size(s) = argSize args 2.
    ⟨⟨281145 + 18848 * argSize args 1⟩, ⟨argSize args 2⟩⟩
  | BuiltinFun.ReplicateByte =>
    -- Source: replicateByte n byte; CEK args = [byte, n].
    -- x = NumBytesCostedAsNumWords(n) where n = args[1]: 0 for n ≤ 0, else (n-1)/8+1.
    let x := match (args[1]? : Option CekValue) with
      | some (CekValue.VCon (Const.Integer n)) =>
          if n ≤ 0 then 0 else (n.toNat - 1) / 8 + 1
      | _ => 0
    ⟨⟨180194 + 159 * x⟩, ⟨1 + 1 * x⟩⟩
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
    -- Source: expModInteger b e m; CEK args = [m, e, b].
    -- CPU: exp_mod_cost; aa=size(b)=args[2], ee=size(e)=args[1], mm=size(m)=args[0].
    -- cost0 = c00 + c11*ee*mm + c12*ee*mm^2; if aa > mm: cost0 + cost0/2.
    -- Memory: linear_in_z (intercept 0, slope 1) = size(m) = argSize args 0.
    let mm := argSize args 0
    let ee := argSize args 1
    let aa := argSize args 2
    let cost0 := 607153 + 231697 * ee * mm + 53144 * ee * mm^2
    ⟨⟨if aa > mm then cost0 + cost0 / 2 else cost0⟩, ⟨mm⟩⟩
  | BuiltinFun.DropList =>
    -- Source: dropList n xs; after force, CEK args = [xs, n].
    -- Model: linear_in_x where x = IntegerCostedLiterally(n) = |n|; n = args[1].
    let x := match (args[1]? : Option CekValue) with
      | some (CekValue.VCon (Const.Integer n)) => n.natAbs
      | _ => 0
    ⟨⟨116711 + 1957 * x⟩, ⟨4⟩⟩

def builtinCostSelected (semVar: BuiltinSemanticsVariant) (b : BuiltinFun) (args : List CekValue) : ExBudget :=
  match semVar with
  | .defaultFunSemanticsVariantA => builtinCostsA b args
  | .defaultFunSemanticsVariantB => builtinCostsB b args
  | .defaultFunSemanticsVariantC => builtinCostsC b args

end PlutusCore.UPLC.CostModels
