import PlutusCore.ByteString
import PlutusCore.Integer

namespace PlutusCore.Data
open PlutusCore.Integer PlutusCore.ByteString

/-! ## Formalisation for PlutusCore Data representation and Builtin functions. -/

namespace PlutusCore.DataInternal

-- Lean definition of Data
inductive Data where
  | Constr : Integer → List Data → Data
  | Map : List (Data × Data) → Data
  | List : List Data → Data
  | I : Integer → Data
  | B : ByteString → Data

mutual
  private def dataStr : Data → String
    | .Constr idx fields => constrStr idx fields
    | .Map mxs => mapStr "" mxs
    | .List xs => listDataStr "" xs
    | .I i => s!"(I {i})"
    | .B bs => s!"(B {bs})"

  private def constrStr : Integer → List Data → String
   | idx, fields =>  s!"(Constr {idx} [{listDataStr "" fields}])"

  private def listDataStr (acc : String) : List Data → String
    | [] => s!"(List [{acc}])"
    | h :: tl =>
        let hStr := dataStr h
        if acc.isEmpty
        then listDataStr hStr tl
        else listDataStr s!"{acc}, {hStr}" tl

  private def mapStr (acc : String) : List (Data × Data) → String
    | [] => s!"(Map [{acc}])"
    | (x, y) :: tl =>
       let hstr := s!"({dataStr x}, {dataStr y})"
       if acc.isEmpty
       then mapStr hstr tl
       else mapStr s!"{acc}, {hstr}" tl
end

/-- ToString instance for Data -/
instance : ToString Data where
  toString := dataStr

/-- Repr instance for Data -/
instance : Repr Data where
  reprPrec x _ := dataStr x


mutual
  def eqData : Data → Data → Bool
    | .Constr i args, .Constr i' args' => eqDataConstr i args i' args'
    | .Map m, .Map m' => eqDataMap m m'
    | .List l, .List l' => eqDataList l l'
    | .I i, .I i' => i == i'
    | .B b, .B b' => b == b'
    | _ , _ => false

  def eqDataList : List Data → List Data → Bool
    | [] , [] => true
    | x :: xs, y :: ys => eqData x y && eqDataList xs ys
    | _ , _ => false

  def eqDataMap : List (Data × Data) → List (Data × Data) → Bool
    | [] , [] => true
    | (x, y) :: xs, (x', y') :: ys => eqData x x' && eqData y y' && eqDataMap xs ys
    | _ , _ => false

  def eqDataConstr : Integer → List Data → Integer → List Data → Bool
    | i , args , i' , args' => (i == i') && eqDataList args args'
end

/-- BEq instance for Data -/
instance BEqData : BEq Data where
  beq := eqData

mutual
  def ltData : Data → Data → Bool
    | .Constr i args, .Constr i' args' => ltDataConstr i args i' args'
    | .Map m, .Map m' => ltDataMap m m'
    | .List l, .List l' => ltDataList l l'
    | .I i, .I i' => i < i'
    | .B b, .B b' => b < b'
    | .Constr .., _ => true
    | _, .Constr .. => false
    | .Map .., _ => true
    | _, .Map .. => false
    | .List .., _ => true
    | _, .List .. => false
    | .I _, _ => true
    | _, .I _ => false

  def ltDataList : List Data → List Data → Bool
    | [] , [] => false
    | [] , _ => true
    | _, [] => false
    | x :: xs, y :: ys =>
         ltData x y || ( x == y && ltDataList xs ys)

  def ltDataMap : List (Data × Data) → List (Data × Data) → Bool
    | [] , [] => false
    | [], _ => true
    | _, [] => false
    | (x, y) :: xs, (x', y') :: ys =>
        ltData x x' || (x == x' && (ltData y y' || (y == y' && ltDataMap xs ys)))

  def ltDataConstr : Integer → List Data → Integer → List Data → Bool
    | i , args , i' , args' => i < i' && ltDataList args args'
end

def Data.compareData (d1 : Data) (d2: Data) : Ordering :=
  if ltData d1 d2 then .lt
  else if d1 == d2 then .eq
  else .gt

/-- LT instance for Data -/
 instance LTData : LT Data where
   lt x y := ltData x y

/-- Ord instance for Data -/
instance OrdData : Ord Data where
  compare x y := Data.compareData x y

@[simp] theorem Data.compare_rlf (x y : Data) : compare x y = Data.compareData x y := rfl

@[simp] theorem Data.compareData_rlf (x y : Data) :
  Data.compareData x y =
  if ltData x y then .lt else if x == y then .eq else .gt := rfl

/-! DecidableLT instance for Data -/

theorem ltData_true_imp_lt (x y : Data) : ltData x y -> x < y := by
  match x, y with
  | .Constr i xs, .Constr j ys => simp [ltData, ltDataConstr, LT.lt]
  | .Map xm, .Map ym => simp [ltData, LT.lt]
  | .List xs, .List ys => simp [ltData, LT.lt]
  | .I i, .I j => simp [ltData, LT.lt]
  | .B bs1, .B bs2 => simp only [ltData, LT.lt]; intro; assumption
  | .Constr .., .Map _
  | .Constr .., .List _
  | .Constr .., .I _
  | .Constr .., .B _
  | .Map _, .List _
  | .Map _, .I _
  | .Map _, .B _
  | .List _, .I _
  | .List _, .B _
  | .I _, .B _ => simp [ltData, LT.lt]
  | .Map _, .Constr ..
  | .List _, .Constr ..
  | .I _, .Constr ..
  | .B _, .Constr ..
  | .List _, .Map _
  | .I _, .Map _
  | .B _, .Map _
  | .I _, .List ..
  | .B _, .List ..
  | .B _ , .I _ => simp [ltData]

theorem ltData_false_imp_not_lt (x y : Data) : ltData x y = false -> ¬ x < y := by
  match x, y with
  | .Constr i xs, .Constr j ys => simp [ltData, ltDataConstr, LT.lt]
  | .Map xm, .Map ym => simp [ltData, LT.lt]
  | .List xs, .List ys => simp [ltData, LT.lt]
  | .I i, .I j => simp [ltData, LT.lt]
  | .B bs1, .B bs2 =>
      simp only [ltData, LT.lt];
      unfold Not; intro h1 h2
      rw [h1] at h2
      contradiction
  | .Constr .., .Map _
  | .Constr .., .List _
  | .Constr .., .I _
  | .Constr .., .B _
  | .Map _, .List _
  | .Map _, .I _
  | .Map _, .B _
  | .List _, .I _
  | .List _, .B _
  | .I _, .B _ => simp [ltData, LT.lt]
  | .Map _, .Constr ..
  | .List _, .Constr ..
  | .I _, .Constr ..
  | .B _, .Constr ..
  | .List _, .Map _
  | .I _, .Map _
  | .B _, .Map _
  | .I _, .List ..
  | .B _, .List ..
  | .B _ , .I _ => simp [ltData, LT.lt]

def Data.decLt (x y : Data) : Decidable (LT.lt x y) :=
  match h:(ltData x y) with
  | true => isTrue (ltData_true_imp_lt _ _ h)
  | false => isFalse (ltData_false_imp_not_lt _ _ h)

instance : DecidableLT Data := Data.decLt

/-! DecidableEq instance for Data -/

mutual
  theorem eqData_true_imp_eq (x y : Data) : eqData x y → x = y := by
    match x, y with
    | .Constr i xs, .Constr j ys =>
         simp [eqData, eqDataConstr]
         intro h1 h2
         apply And.intro
         . assumption
         . apply eqDataList_true_imp_eq _ _ h2
    | .List xs, .List ys =>
         simp [eqData]
         apply eqDataList_true_imp_eq
    | .Map xm, .Map ym =>
         simp [eqData]
         apply eqDataMap_true_imp_eq xm ym
    | .I i, .I j => simp [eqData]
    | .B bs1, .B bs2 =>
       simp only [eqData]
       intro h1
       have h2 : bs1 = bs2 := BEqByteString_true_imp_eq _ _ h1
       rw [h2]
    | .Constr .., .List _
    | .Constr .., .Map _
    | .Constr .., .I _
    | .Constr .., .B _
    | .List _, .Constr ..
    | .List _, .Map _
    | .List _, .I _
    | .List _, .B _
    | .Map _, .Constr ..
    | .Map _, .List _
    | .Map _, .I _
    | .Map _, .B _
    | .I _, .Constr ..
    | .I _, .List _
    | .I _, .Map _
    | .I _, .B _
    | .B _, .Constr ..
    | .B _, .List _
    | .B _, .Map _
    | .B _, .I _ =>
         simp [eqData]

  theorem eqDataList_true_imp_eq (xs ys : List Data) : eqDataList xs ys → xs = ys := by
    match xs, ys with
    | [], []
    | [], _ :: _
    | _ :: _,  [] => simp [eqDataList]
    | hd1 :: tl1, hd2 :: tl2 =>
       simp [eqDataList]
       intro h1 h2
       apply And.intro
       . apply eqData_true_imp_eq _ _ h1
       . apply eqDataList_true_imp_eq tl1 tl2 h2

  theorem eqDataMap_true_imp_eq (xs ys : List (Data × Data)) : eqDataMap xs ys → xs = ys := by
    match xs, ys with
    | [], []
    | [], _ :: _
    | _ :: _,  [] => simp [eqDataMap]
    | (x, y) :: tl1, (x', y') :: tl2 =>
        simp [eqDataMap]
        intro h1 h2 h3
        apply And.intro
        . apply And.intro
          . apply eqData_true_imp_eq _ _ h1
          . apply eqData_true_imp_eq _ _ h2
        . apply eqDataMap_true_imp_eq _ _ h3

end

mutual
  theorem eqData_false_imp_not_eq (x y : Data) : eqData x y = false → x ≠ y := by
    match x, y with
    | .Constr i xs, .Constr j ys =>
         simp [eqData, eqDataConstr]
         intro h1 h2
         have h3 : eqDataList xs ys = false := h1 h2
         apply eqDataList_false_imp_not_eq _ _ h3
    | .List xs, .List ys =>
         simp [eqData]
         apply eqDataList_false_imp_not_eq xs ys
    | .Map xm, .Map ym =>
         simp [eqData]
         apply eqDataMap_false_imp_not_eq xm ym
    | .I i, .I j => simp [eqData]
    | .B bs1, .B bs2 => simp [eqData]
    | .Constr _ _, .List _
    | .Constr _ _, .Map _
    | .Constr _ _, .I _
    | .Constr _ _, .B _
    | .List _, .Constr _ _
    | .List _, .Map _
    | .List _, .I _
    | .List _, .B _
    | .Map _, .Constr _ _
    | .Map _, .List _
    | .Map _, .I _
    | .Map _, .B _
    | .I _, .Constr _ _
    | .I _, .List _
    | .I _, .Map _
    | .I _, .B _
    | .B _, .Constr _ _
    | .B _, .List _
    | .B _, .Map _
    | .B _, .I _ => simp [eqData]

  theorem eqDataList_false_imp_not_eq (xs ys : List Data) : eqDataList xs ys = false → xs ≠ ys := by
    match xs, ys with
    | [], []
    | [], _ :: _
    | _ :: _,  [] => simp [eqDataList]
    | hd1 :: tl1, hd2 :: tl2 =>
       simp only [eqDataList]
       rw [Bool.and_eq_false_iff]
       intro h1
       simp; intro h2
       apply Or.elim h1 <;> intro h3
       . have h4 : hd1 ≠ hd2 := eqData_false_imp_not_eq _ _ h3
         contradiction
       . apply eqDataList_false_imp_not_eq tl1 tl2 h3

  theorem eqDataMap_false_imp_not_eq (xs ys : List (Data × Data)) : eqDataMap xs ys = false → xs ≠ ys := by
    match xs, ys with
    | [], []
    | [], _ :: _
    | _ :: _,  [] => simp [eqDataMap]
    | (x, y) :: tl1, (x', y') :: tl2 =>
        simp only [eqDataMap]
        rw [Bool.and_eq_false_iff]
        intro h1
        simp; intro h2 h3
        apply Or.elim h1 <;> intro h4
        . rw [Bool.and_eq_false_iff] at h4
          apply Or.elim h4 <;> intro h5
          . have h6 : x ≠ x' := eqData_false_imp_not_eq _ _ h5
            contradiction
          . have h6 : y ≠ y' := eqData_false_imp_not_eq _ _ h5
            contradiction
        . apply eqDataMap_false_imp_not_eq tl1 tl2 h4
end

def Data.decEq (x y : Data) : Decidable (Eq x y) :=
  match h:(eqData x y) with
  | true => isTrue (eqData_true_imp_eq _ _ h)
  | false => isFalse (eqData_false_imp_not_eq _ _ h)

instance : DecidableEq Data := Data.decEq

/-! LawfulBEq instance for Data -/
mutual
  theorem eqData_reflexive (x : Data) : eqData x x = true := by
    match x with
    | .Constr i xs =>
        simp [eqData, eqDataConstr]
        apply eqDataList_reflexive xs
    | .List xs =>
        simp [eqData]
        apply eqDataList_reflexive xs
    | .Map xm =>
        simp [eqData]
        apply eqDataMap_reflexive xm
    | .I i => simp [eqData]
    | .B bs => simp [eqData]

  theorem eqDataList_reflexive (xs : List Data) : eqDataList xs xs = true := by
    match xs with
    | [] => simp [eqDataList]
    | h :: tl =>
        simp [eqDataList]
        apply And.intro
        . apply eqData_reflexive
        . apply eqDataList_reflexive

  theorem eqDataMap_reflexive (xs : List (Data × Data)) : eqDataMap xs xs = true := by
    match xs with
    | [] => simp [eqDataMap]
    | (x, y) :: tl =>
        simp [eqDataMap]
        apply And.intro
        . apply And.intro <;> apply eqData_reflexive
        . apply eqDataMap_reflexive
end

instance LawfulBEqData : LawfulBEq Data where
  eq_of_beq := by simp [BEq.beq]; apply eqData_true_imp_eq
  rfl := by simp [BEq.beq]; apply eqData_reflexive


mutual
@[simp] theorem ltData_irrefl (x : Data) : ¬ ltData x x := by
    match x with
    | .Constr i xs => simp [ltData, ltDataConstr]
    | .List xs =>
         simp only [ltData]
         apply ltDataList_irrefl
    | .Map xm =>
         simp only [ltData]
         apply ltDataMap_irrefl
    | .I i => simp [ltData]
    | .B bs => simp [ltData]

@[simp] theorem ltDataList_irrefl (xs : List Data) : ¬ ltDataList xs xs := by
    match xs with
    | [] => simp [ltDataList]
    | hd :: tl =>
       simp [ltDataList]
       apply And.intro
       . have h := ltData_irrefl hd
         simp at h
         assumption
       . have h := ltDataList_irrefl tl
         simp at h
         assumption

@[simp] theorem ltDataMap_irrefl (xs : List (Data × Data)) : ¬ ltDataMap xs xs := by
    match xs with
    | [] => simp [ltDataMap]
    | (x, y) :: tl =>
        simp [ltDataMap]
        apply And.intro
        . have h := ltData_irrefl x
          simp at h
          assumption
        . apply And.intro
          . have h := ltData_irrefl y
            simp at h
            assumption
          . have h := ltDataMap_irrefl tl
            simp at h
            assumption
end

@[simp] theorem Data.lt_irrefl (x : Data) : ¬ x < x := by
  simp [LT.lt]

/-! Std.Irrefl instance for Data -/
instance : Std.Irrefl (. < . : Data → Data → Prop) where
  irrefl := Data.lt_irrefl


/-! ## Builtin Data functions. -/

/-- Given `d` a Data instance, `chooseData d tc tm tl ti tb` is defined as follows:
     := tc   if d = Constr _ _
     := tm   if d = Map _
     := tl   if d = List _
     := ti   if d = I _
     := tb   if d = B

    NOTE: `chooseData` is defined as a macro rule mainly for Lean to
    be able to detect that functions recursively defined using `caseData` satisfy
    strutural recursion.

    Signature:
     `chooseData : Data → α → α → α → α → α → α
-/
macro_rules
 | `(UPLC.chooseData $d $tc $tm $tl $ti $tb) =>
      -- trick to use match expression in macro_rules by using an existing one (i.e., dataStr match)
      `(dataStr.match_1 (fun (_ : Data) => _) $d
        (fun (i : Integer) (ds : List Data) => $tc)
        (fun (ps : List (Data × Data)) => $tm)
        (fun (xs : List Data) => $tl)
        (fun (i : Integer) => $ti)
        (fun (bs : ByteString) => $tb))

/-- Given `d` a Data instance, `caseData d fc fm fl fi fb` is defined as follows:
     := fc i ds   if d = Constr i ds
     := fm ps     if d = Map ps
     := fl xs     if d = List xs
     := fi i      if d = I i
     := fb bs     if d = B bs
    NOTE: `caseData` is defined as a macro rule mainly for Lean to
    be able to detect that functions recursively defined using `caseData` satisfy
    strutural recursion.

    Signature:
     `caseData :
      (Integer → List Data → α) →
      (List (Data × Data) → α) →
      (List Data → α) →
      (Integer → α) →
      (ByteString → α) →
      Data →
      α
-/
macro_rules
 | `(UPLC.caseData $fc $fm $fl $fi $fb $d) =>
      -- trick to use match expression in macro_rules by using an existing one (i.e., dataStr match)
      `(dataStr.match_1 (fun (_ : Data) => _) $d
        (fun (i : Integer) (ds : List Data) => $fc i ds)
        (fun (ps : List (Data × Data)) => $fm ps)
        (fun (xs : List Data) => $fl xs)
        (fun (i : Integer) => $fi i)
        (fun (bs : ByteString) => $fb bs))

/-- Given `idx` and `fields` return `Constr idx fields` -/
def constrData (idx : Integer) (fields : List Data) : Data :=
  .Constr idx fields

/-- Given `maps` return `Map maps` -/
def mapData (maps : List (Data × Data)) : Data := .Map maps

/-- Given `xs` return `List xs` -/
def listData (xs : List Data) : Data := .List xs

/-- Given `i` return `I i` -/
def iData (i : Integer) : Data := .I i

/-- Given `bs` return `B bs` -/
def bData (bs : ByteString) : Data := .B bs

/-- Given `d` a Data instance, perform the following:
     - When d := `Constr idx fields`
         - return `(idx, fields)`
     - Otherwise
         - return ⊥
-/
def unConstrData (d : Data) : Except String (Integer × List Data) :=
  match d with
  | .Constr idx fields => pure (idx, fields)
  | _ => throw "unConstrData: not a Constr"

/-- Given `d` a Data instance, perform the following:
     - When `d := Map maps`
         - return `maps`
     - Otherwise
         - return ⊥
-/
def unMapData (d : Data) : Except String (List (Data × Data)) :=
  match d with
  | .Map map => pure map
  | _ => throw "unMapData: not a Map"

/-- Given `d` a Data instance, perform the following:
     - When `d := List xs`
         - return `xs`
     - Otherwise
         - return ⊥
-/
def unListData (d : Data) : Except String (List Data) :=
  match d with
  | .List xs => pure xs
  | _ => throw "unListData: not a List"

/-- Given `d` a Data instance, perform the following:
     - When `d := I i`
         - return `i`
     - Otherwise
         - return ⊥
-/
def unIData (d : Data) : Except String Integer :=
  match d with
  | .I i => pure i
  | _ => throw "unIData: not an I"


/-- Given `d` a Data instance, perform the following:
     - When `d := B bs`
         - return `bs`
     - Otherwise
         - return ⊥
-/
def unBData (d : Data) : Except String ByteString :=
  match d with
  | .B bs => pure bs
  | _ => throw "unBData: not a B"

/- Return `true` only when `d1 == d2` -/
def equalsData (d1 : Data) (d2 : Data) : Bool := d1 == d2

/-- Return (d1, d2) --/
def mkPairData (d1 : Data) (d2 : Data) : Data × Data := (d1, d2)

/-- Return `[]` --/
def mkNilData (_u : Unit) : List Data := []

/-- Return `[]` --/
def mkNilPairData (_u : Unit) : List (Data × Data) := []

-- TODO: serialiseData : Data → ByteString

end PlutusCore.DataInternal

export PlutusCore.DataInternal
  -- NOTE: macro rules chooseData and caseData are implicitly exported
  ( -- type
   Data
   Data.Constr
   Data.Map
   Data.List
   Data.I
   Data.B
   -- intermediate definitions
   eqData
   eqDataMap
   eqDataList
   eqDataConstr
   ltData
   ltDataMap
   ltDataList
   ltDataConstr
   -- builtin functions
   bData
   constrData
   equalsData
   iData
   listData
   mapData
   mkNilData
   mkNilPairData
   mkPairData
   unBData
   unConstrData
   unIData
   unListData
   unMapData
   -- theorems
   Data.compare_rlf
   Data.compareData_rlf
   eqData_true_imp_eq
   eqDataList_true_imp_eq
   eqDataMap_true_imp_eq
   eqData_false_imp_not_eq
   eqDataList_false_imp_not_eq
   eqDataMap_false_imp_not_eq
   eqData_reflexive
   eqDataList_reflexive
   eqDataMap_reflexive
   ltData_irrefl
   ltDataList_irrefl
   ltDataMap_irrefl
  )

end PlutusCore.Data
