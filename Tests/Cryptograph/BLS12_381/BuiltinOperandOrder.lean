import PlutusCore.UPLC
import Blaster

/-! The BLS12-381 builtins apply their operands in order.

The CEK machine hands a builtin its arguments last-first. `bls12381G1Add`, `G1Equal`,
`G2Add`, `G2Equal`, `MulMlResult` and `FinalVerify` used to match that list as `[x, y]`
and call `f x y`, so `add(a, b)` ran as `add(b, a)`. Each is commutative or symmetric on
real values, so evaluation never showed it; but the builtins are `opaque`, and to the
solver `add(a, b)` and `add(b, a)` are different terms. Each program below combines two
of them so that only the in-order reading is Valid. -/

namespace Cryptograph.BLS12_381.BuiltinOperandOrder
open PlutusCore.UPLC.Term (Term Const)
open PlutusCore.UPLC.CekMachine (State)
open PlutusCore.Crypto.BLS12_381.G1
open PlutusCore.Crypto.BLS12_381.G2
open PlutusCore.Crypto.BLS12_381.Pairing

-- `(lam a (lam b [equal [add a b] a]))`, over G1, then over G2
#import_uplc g1OrderScript PlutusV3 textual "Tests/Cryptograph/BLS12_381/g1_operand_order.uplc"
#import_uplc g2OrderScript PlutusV3 textual "Tests/Cryptograph/BLS12_381/g2_operand_order.uplc"
-- `(lam a (lam b (lam c (lam d [finalVerify [mulMlResult [millerLoop a b] [millerLoop c d]] [millerLoop a b]]))))`
#import_uplc pairingOrderScript PlutusV3 textual "Tests/Cryptograph/BLS12_381/pairing_operand_order.uplc"

def g1Args (a b : BLS12_381_G1_Element) : List Term :=
  [Term.Const (Const.Bls12_381_G1_element a), Term.Const (Const.Bls12_381_G1_element b)]
def g2Args (a b : BLS12_381_G2_Element) : List Term :=
  [Term.Const (Const.Bls12_381_G2_element a), Term.Const (Const.Bls12_381_G2_element b)]
def pairingArgs (a : BLS12_381_G1_Element) (b : BLS12_381_G2_Element)
    (c : BLS12_381_G1_Element) (d : BLS12_381_G2_Element) : List Term :=
  [Term.Const (Const.Bls12_381_G1_element a), Term.Const (Const.Bls12_381_G2_element b),
   Term.Const (Const.Bls12_381_G1_element c), Term.Const (Const.Bls12_381_G2_element d)]

#prep_uplc g1Order g1OrderScript g1Args 200
#prep_uplc g2Order g2OrderScript g2Args 200
#prep_uplc pairingOrder pairingOrderScript pairingArgs 200

/-- The run halts with the boolean `b`. A match, so the solver never sees the whole CEK
    datatype (see `Tests/BlueprintVerify/BooleanCase.lean`). -/
def haltsWithBool (s : State) (b : Bool) : Prop :=
  match s with
  | .Halt (.VCon (.Bool c)) => c = b
  | _ => False

theorem g1_operands_in_order : ∀ (a b : BLS12_381_G1_Element),
    haltsWithBool (g1Order.prop a b) (bls12_381_G1_equal (bls12_381_G1_add a b) a) := by blaster

theorem g2_operands_in_order : ∀ (a b : BLS12_381_G2_Element),
    haltsWithBool (g2Order.prop a b) (bls12_381_G2_equal (bls12_381_G2_add a b) a) := by blaster

theorem pairing_operands_in_order : ∀ (a : BLS12_381_G1_Element) (b : BLS12_381_G2_Element)
    (c : BLS12_381_G1_Element) (d : BLS12_381_G2_Element),
    haltsWithBool (pairingOrder.prop a b c d)
      (bls12_381_finalVerify
        (bls12_381_mulMlResult (bls12_381_millerLoop a b) (bls12_381_millerLoop c d))
        (bls12_381_millerLoop a b)) := by blaster

end Cryptograph.BLS12_381.BuiltinOperandOrder
