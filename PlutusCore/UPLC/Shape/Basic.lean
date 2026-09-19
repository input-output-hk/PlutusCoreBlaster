import PlutusCore.UPLC.Term

/-!
# UPLC success-typing shape analyzer

A best-effort **success typing** for compiled UPLC: an over-approximation of the values each
argument can take without the script crashing.  The inferred argument shapes are *necessary*
conditions ("pass something outside this shape and it will fail") — being inside a shape is not
a proof of success.  The analysis never rejects; where it cannot tell, it degrades to
`Anything`.

Design (each stage has its own `## …` section below):
* a lattice `TermShape` / `DataShape` with `Anything` (⊤), `Nothing` (⊥), unions, and
  positional structure for lists / pairs / `Data` / SOP `Constr`;
* `meet` (refine a demand) and `join` (merge branch results) instead of a single `unify`;
* structural discovery of `Data`/list/pair arguments via structural builtin shapes + `meet`
  with shared refinement cells;
* `choose`/`if` builtins fork-and-join their branches so heterogeneous branches yield unions;
* a bounded fixpoint for self-application / recursion.

On top of that baseline the engine applies four call-site *tactics* (referenced by number
throughout the source):
1. **Tag reconstruction.** `unConstrData d` labels the datum's integer tag `ConIntTag d`;
   `equalsInteger tag K` becomes the predicate `BoolPred d K`; a path-sensitive `ifThenElse` on
   that predicate refines `d`'s `Data` to tag `K` in the then-branch
   (`inferUnConstr` / `inferEqualsInteger` / `inferIfThenElse`).
2. **Live-branch narrowing.** A fully-applied `chooseData` narrows its discriminant to the union
   of the variants whose branches are not dead (`Error`) (`narrowChooseData`).
3. **Bounded unrolling.** A variable bound to a lambda (tracked in `Env.funDefs`) is inlined at
   its call site up to `Env.unrollFuel`, so recursive self-calls are analysed a few levels deep
   (`inferBetaRedex`).
4. **Positional list projection.** `headList`/`tailList` navigate a list's known positions
   (head = position 0, tail advances the offset) via growable `ListView`/`FieldsOf` cells,
   instead of collapsing every position to one homogeneous element (`inferProjection`).

The analysis engine is deliberately `partial` (it runs a fuelled fixpoint and is only ever
used as a developer tool / in `#eval` / `native_decide`, never inside kernel proofs); the data
layer is total.
-/

namespace PlutusCore.UPLC.Shape

namespace Internal

open Std

open PlutusCore.UPLC.Term
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

/-! ## Shape lattice -/

mutual

/-- The shape lattice for UPLC values: top `Anything` (⊤, "no information"), bottom `Nothing`
    (⊥, "provably crashes"), unions (`Alternatives`), unification variables (`TypeVar`, resolved
    through `Env` cells), equirecursive `Rec`/`RecVar`, and positional structure for functions,
    `Delay`, SOP `Constr`, lists, pairs and `Data` (`DataSh`). `ListView`/`FieldsOf` are transient
    growable handles that `zonk` resolves away before display. -/
inductive TermShape where
  | Anything
  | Nothing
  | TypeVar       (name : Nat)
  | Alternatives  (options : List TermShape)
  | Function      (input output : TermShape)
  | Delay         (delayed : TermShape)
  /-- Equirecursive (μ) type; `RecVar` refers to the enclosing `Rec` by de Bruijn depth. -/
  | Rec           (body : TermShape)
  | RecVar        (idx : Nat)
  /-- SOP constructor value.  `tag = none` when the tag is not statically known
      (a `Constr` value arriving through a variable / argument). -/
  | Constr        (tag : Option Nat) (fields : List TermShape)
  /-- Positional list: `positions[i]` is element `i`; further elements have shape `rest`
      (`rest = Nothing` ⇒ closed length; `rest = Anything` ⇒ unknown tail). -/
  | ListSh        (positions : List TermShape) (rest : TermShape)
  /-- Growable positional `List` view: its discovered structure lives in `cells[cell]` (a
      `ListSh`), viewed from position `offset`; `head`/`tail` navigate & grow it. -/
  | ListView      (cell : Nat) (offset : Nat)
  /-- Growable positional `Data.Constr` fields view: the `DConstr` lives in `dcells[cell]`,
      viewed from field `offset`; `head`/`tail` navigate & grow its fields. -/
  | FieldsOf      (cell : Nat) (offset : Nat)
  | PairSh        (fst snd : TermShape)
  | DataSh        (d : DataShape)
  | ConInteger
  | ConByteString
  | ConString
  | ConUnit
  | ConBool
  /-- An integer known to be the constructor tag of the `Data` bound to variable `owner`
      (tactic 1: tag reconstruction). Behaves as `ConInteger`. -/
  | ConIntTag     (owner : String)
  /-- A boolean that holds iff `owner`'s `Data` tag equals `tag` (a refinement predicate).
      Behaves as `ConBool`. -/
  | BoolPred      (owner : String) (tag : Nat)
  | ConBls12_381_G1_element
  | ConBls12_381_G2_element
  | ConBls12_381_MlResult

/-- The shape lattice for on-chain `Data`, mirroring `Data`'s five variants (`DConstr`, `DMap`,
    `DList`, `DInt`, `DBytes`) with top `DUnknown` (⊤), bottom `DNone` (⊥), unions (`DAlt`),
    unification variables (`DVar`) and equirecursive `DRec`/`DRecVar`. `DConstr` carries a tail
    (`rest`) so its field list can grow during positional discovery. -/
inductive DataShape where
  | DVar    (name : Nat)
  | DUnknown
  | DNone
  | DRec    (body : DataShape)
  | DRecVar (idx : Nat)
  | DConstr (tag : Option Nat) (fields : List DataShape) (rest : DataShape)
  | DMap    (key val : DataShape)
  | DList   (elem : DataShape)
  | DInt
  | DBytes
  | DAlt    (options : List DataShape)

end

instance : Inhabited TermShape := ⟨.Anything⟩
instance : Inhabited DataShape := ⟨.DUnknown⟩

deriving instance BEq for TermShape, DataShape
deriving instance Repr for TermShape, DataShape

/-! ## Rendering -/

namespace TermShape

private def greekVar (n : Nat) : String :=
  let letters := #["α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "λ", "μ",
                   "ν", "ξ", "ο", "π", "ρ", "σ", "τ", "υ", "φ", "χ", "ψ", "ω"]
  match letters[n]? with
  | some s => s
  | none   => "τ" ++ toString n

private def tagStr : Option Nat → String
  | some n => toString n
  | none   => "?"

mutual

partial def toStr : TermShape → String
  | .Anything                => "Anything"
  | .Nothing                 => "Nothing"
  | .TypeVar n               => greekVar n
  | .Alternatives options    => String.intercalate " | " (options.map parenAlt)
  | .Function input output    =>
      let lhs := match input with
        | .Function _ _ => "(" ++ toStr input ++ ")"
        | _             => toStr input
      lhs ++ " → " ++ toStr output
  | .Delay delayed           => "Delay (" ++ toStr delayed ++ ")"
  | .Rec body                => "μρ. " ++ toStr body
  | .RecVar _                => "ρ"
  | .Constr tag fields =>
      match fields with
      | [] => "Constr " ++ tagStr tag
      | _  => "Constr " ++ tagStr tag ++ " (" ++ String.intercalate ", " (fields.map toStr) ++ ")"
  | .ListSh positions rest =>
      let inner := positions.map toStr
      let all := match rest with
        | .Nothing  => inner
        | .Anything => inner ++ ["…"]
        | r         => inner ++ ["…" ++ toStr r]
      "[" ++ String.intercalate ", " all ++ "]"
  | .ListView _ _            => "[…]"    -- resolved away by `zonk` before display
  | .FieldsOf _ _            => "[…]"    -- resolved away by `zonk` before display
  | .PairSh a b              => "(" ++ toStr a ++ ", " ++ toStr b ++ ")"
  | .DataSh d                => dataToStr d
  | .ConInteger              => "Int"
  | .ConByteString           => "ByteString"
  | .ConString               => "String"
  | .ConUnit                 => "Unit"
  | .ConBool                 => "Bool"
  | .ConIntTag _             => "Int"
  | .BoolPred _ _            => "Bool"
  | .ConBls12_381_G1_element => "G1"
  | .ConBls12_381_G2_element => "G2"
  | .ConBls12_381_MlResult   => "MlResult"

partial def parenAlt (s : TermShape) : String :=
  match s with
  | .Function _ _ => "(" ++ toStr s ++ ")"
  | _             => toStr s

partial def dataToStr : DataShape → String
  | .DVar _     => "Data"    -- unbound data cell: unknown Data
  | .DUnknown   => "Data"
  | .DNone      => "Data⊥"
  | .DRec body  => "μδ. " ++ dataToStr body
  | .DRecVar _  => "δ"
  | .DConstr tag fields rest =>
      -- open tail (`DUnknown`/unbound cell, length never checked) renders `…`; only `DNone` closed
      let fieldStrs := fields.map dataToStr
      let restStr := match rest with
        | .DNone    => []
        | .DUnknown => ["…"]
        | .DVar _   => ["…"]
        | r         => ["…" ++ dataToStr r]
      match fieldStrs with
      | [] => "Data.Constr " ++ tagStr tag    -- nothing discovered
      | _  => "Data.Constr " ++ tagStr tag ++ " (" ++ String.intercalate ", " (fieldStrs ++ restStr) ++ ")"
  | .DMap k v   => "Data.Map (" ++ dataToStr k ++ " → " ++ dataToStr v ++ ")"
  | .DList e    => "Data.List (" ++ dataToStr e ++ ")"
  | .DInt       => "Data.I"
  | .DBytes     => "Data.B"
  | .DAlt opts  => String.intercalate " | " (opts.map dataToStr)

end

instance : ToString TermShape := ⟨toStr⟩

end TermShape

/-! ## Union smart-constructor -/

/-- Flatten nested `Alternatives`, drop `Nothing`, collapse `Anything`, dedup. -/
def mkAlt (shapes : List TermShape) : TermShape :=
  let flat := shapes.flatMap (λ
    | .Alternatives opts => opts
    | .Nothing           => []
    | other              => [other])
  if flat.isEmpty then .Nothing
  else if flat.contains .Anything then .Anything
  else
    let deduped := flat.foldl (λ acc s => if acc.contains s then acc else acc ++ [s]) []
    match deduped with
    | []  => .Nothing
    | [s] => s
    | _   => .Alternatives deduped

def mkAltD (shapes : List DataShape) : DataShape :=
  let flat := shapes.flatMap (λ
    | .DAlt opts => opts
    | .DNone     => []
    | other      => [other])
  if flat.isEmpty then .DNone
  else if flat.contains .DUnknown then .DUnknown
  else
    let deduped := flat.foldl (λ acc s => if acc.contains s then acc else acc ++ [s]) []
    match deduped with
    | []  => .DNone
    | [s] => s
    | _   => .DAlt deduped

/-! ## Environment + cells -/

structure Env where
  vars       : HashMap String TermShape   -- accumulated demand per variable
  cells      : HashMap Nat TermShape      -- TypeVar bindings
  dcells     : HashMap Nat DataShape      -- DVar bindings
  next       : Nat                        -- fresh cell counter
  fuel       : Nat                        -- fixpoint budget
  funDefs    : HashMap String Term        -- variables bound to a lambda term (tactic 3)
  unrollFuel : Nat                        -- bounded recursion-unrolling budget (tactic 3)

instance : Inhabited Env :=
  ⟨{ vars       := HashMap.emptyWithCapacity
   , cells      := HashMap.emptyWithCapacity
   , dcells     := HashMap.emptyWithCapacity
   , next       := 0
   , fuel       := 0
   , funDefs    := HashMap.emptyWithCapacity
   , unrollFuel := 0
   }⟩

namespace Env

def defaultFuel       : Nat := 8
def defaultUnrollFuel : Nat := 2

def empty : Env :=
  { vars       := HashMap.emptyWithCapacity
  , cells      := HashMap.emptyWithCapacity
  , dcells     := HashMap.emptyWithCapacity
  , next       := 0
  , fuel       := defaultFuel
  , funDefs    := HashMap.emptyWithCapacity
  , unrollFuel := defaultUnrollFuel
  }

def getVar (e : Env) (name : String) : TermShape := e.vars.getD name .Anything
def setVar (e : Env) (name : String) (s : TermShape) : Env := { e with vars := e.vars.insert name s }
def eraseVar (e : Env) (name : String) : Env := { e with vars := e.vars.erase name }

def fresh  (e : Env) : TermShape × Env := (.TypeVar e.next, { e with next := e.next + 1 })
def freshD (e : Env) : DataShape × Env := (.DVar    e.next, { e with next := e.next + 1 })

def setCell  (e : Env) (n : Nat) (s : TermShape) : Env := { e with cells  :=  e.cells.insert n s }
def setDCell (e : Env) (n : Nat) (d : DataShape) : Env := { e with dcells := e.dcells.insert n d }

/-- One-step head resolution of a term-shape cell. -/
partial def resolve (e : Env) : TermShape → TermShape
  | .TypeVar n =>
      match e.cells[n]? with
      | some s => resolve e s
      | none   => .TypeVar n
  | s => s

partial def resolveD (e : Env) : DataShape → DataShape
  | .DVar n =>
      match e.dcells[n]? with
      | some d => resolveD e d
      | none   => .DVar n
  | d => d

end Env

/-! ## Deep resolution (for display) -/

mutual
/-- Deep resolution for display: recursively substitutes every `TypeVar`/`DVar` cell, re-applies
    the union smart-constructors, and materialises growable `ListView`/`FieldsOf` handles into
    concrete `ListSh`s (positions taken from the view's offset). Run once, just before rendering. -/
partial def zonk (e : Env) : TermShape → TermShape
  | .TypeVar n       =>
      match e.cells[n]? with
      | some s => zonk e s
      | none   => .TypeVar n
  | .Alternatives os => mkAlt (os.map (zonk e))
  | .Function i o    => .Function (zonk e i) (zonk e o)
  | .Delay d         => .Delay (zonk e d)
  | .Constr tag fs   => .Constr tag (fs.map (zonk e))
  | .ListSh ps r     => .ListSh (ps.map (zonk e)) (zonk e r)
  | .ListView c off  =>
      match zonk e (.TypeVar c) with
      | .ListSh ps r => .ListSh (ps.drop off) r
      | _            => .ListSh [] .Anything
  | .FieldsOf c off  =>
      match zonkD e (.DVar c) with
      | .DConstr _ fs r =>
          let tail := match r with
            | .DNone    => .Nothing
            | .DUnknown => .Anything
            | r'        => .DataSh r'
          .ListSh ((fs.drop off).map (.DataSh ·)) tail
      | _ => .ListSh [] (.DataSh .DUnknown)
  | .PairSh a b      => .PairSh (zonk e a) (zonk e b)
  | .DataSh d        => .DataSh (zonkD e d)
  | .Rec b           => .Rec (zonk e b)
  | s                => s
partial def zonkD (e : Env) : DataShape → DataShape
  | .DVar n           =>
      match e.dcells[n]? with
      | some d => zonkD e d
      | none   => .DVar n
  | .DRec b           => .DRec (zonkD e b)
  | .DConstr tag fs r => .DConstr tag (fs.map (zonkD e)) (zonkD e r)
  | .DMap k v         => .DMap (zonkD e k) (zonkD e v)
  | .DList el         => .DList (zonkD e el)
  | .DAlt os          => mkAltD (os.map (zonkD e))
  | d                 => d
end

/-! ## Equirecursive (μ) type machinery -/

partial def occursVar (target : Nat) : TermShape → Bool
  | .TypeVar n       => n == target
  | .Alternatives os => os.any (occursVar target)
  | .Function i o    => occursVar target i || occursVar target o
  | .Delay d         => occursVar target d
  | .Constr _ fs     => fs.any (occursVar target)
  | .ListSh ps r     => ps.any (occursVar target) || occursVar target r
  | .PairSh a b      => occursVar target a || occursVar target b
  | .Rec b           => occursVar target b
  | _                => false

/-- Replace `TypeVar target` with `RecVar depth`, shifting under nested `Rec`. -/
partial def abstractVar (target depth : Nat) : TermShape → TermShape
  | .TypeVar n       => if n == target then .RecVar depth else .TypeVar n
  | .Alternatives os => .Alternatives (os.map (abstractVar target depth))
  | .Function i o    => .Function (abstractVar target depth i) (abstractVar target depth o)
  | .Delay d         => .Delay (abstractVar target depth d)
  | .Constr t fs     => .Constr t (fs.map (abstractVar target depth))
  | .ListSh ps r     => .ListSh (ps.map (abstractVar target depth)) (abstractVar target depth r)
  | .PairSh a b      => .PairSh (abstractVar target depth a) (abstractVar target depth b)
  | .Rec b           => .Rec (abstractVar target (depth + 1) b)
  | other            => other

/-- Substitute `RecVar depth` with `repl`, shifting under nested `Rec`. -/
partial def substRec (depth : Nat) (repl : TermShape) : TermShape → TermShape
  | .RecVar i        => if i == depth then repl else .RecVar i
  | .Alternatives os => .Alternatives (os.map (substRec depth repl))
  | .Function i o    => .Function (substRec depth repl i) (substRec depth repl o)
  | .Delay d         => .Delay (substRec depth repl d)
  | .Constr t fs     => .Constr t (fs.map (substRec depth repl))
  | .ListSh ps r     => .ListSh (ps.map (substRec depth repl)) (substRec depth repl r)
  | .PairSh a b      => .PairSh (substRec depth repl a) (substRec depth repl b)
  | .Rec b           => .Rec (substRec (depth + 1) repl b)
  | other            => other

/-- One-step unfolding of an equirecursive type: `μρ.F ≡ F[μρ.F/ρ]`. -/
def unfoldRec : TermShape → TermShape
  | .Rec b => substRec 0 (.Rec b) b
  | s      => s

partial def occursDVar (target : Nat) : DataShape → Bool
  | .DVar n           => n == target
  | .DConstr _ fs r   => fs.any (occursDVar target) || occursDVar target r
  | .DMap k v         => occursDVar target k || occursDVar target v
  | .DList el         => occursDVar target el
  | .DAlt os          => os.any (occursDVar target)
  | .DRec b           => occursDVar target b
  | _                 => false

partial def abstractDVar (target depth : Nat) : DataShape → DataShape
  | .DVar n           => if n == target then .DRecVar depth else .DVar n
  | .DConstr t fs r   => .DConstr t (fs.map (abstractDVar target depth)) (abstractDVar target depth r)
  | .DMap k v         => .DMap (abstractDVar target depth k) (abstractDVar target depth v)
  | .DList el         => .DList (abstractDVar target depth el)
  | .DAlt os          => .DAlt (os.map (abstractDVar target depth))
  | .DRec b           => .DRec (abstractDVar target (depth + 1) b)
  | other             => other

partial def substDRec (depth : Nat) (repl : DataShape) : DataShape → DataShape
  | .DRecVar i        => if i == depth then repl else .DRecVar i
  | .DConstr t fs r   => .DConstr t (fs.map (substDRec depth repl)) (substDRec depth repl r)
  | .DMap k v         => .DMap (substDRec depth repl k) (substDRec depth repl v)
  | .DList el         => .DList (substDRec depth repl el)
  | .DAlt os          => .DAlt (os.map (substDRec depth repl))
  | .DRec b           => .DRec (substDRec (depth + 1) repl b)
  | other             => other

def unfoldDRec : DataShape → DataShape
  | .DRec b => substDRec 0 (.DRec b) b
  | d       => d

/-- Bind a term-cell, tying the knot into a `Rec` if the binding would be cyclic. -/
def bindCell (e : Env) (x : Nat) (s : TermShape) : Env :=
  match s with
  | .ListView _ _ | .FieldsOf _ _ => e.setCell x s   -- preserve growable-view identity (no zonk)
  | _ =>
      let sZ := zonk e s
      if occursVar x sZ
        then e.setCell x (.Rec (abstractVar x 0 sZ))
        else e.setCell x s

def bindDCell (e : Env) (x : Nat) (d : DataShape) : Env :=
  let dZ := zonkD e d
  if occursDVar x dZ
    then e.setDCell x (.DRec (abstractDVar x 0 dZ))
    else e.setDCell x d

/-! ## Growable-view resolution -/

/-- Follow `TypeVar`/`DVar` chains to the canonical cell holding a view's structure. -/
partial def canonCell (e : Env) (c : Nat) : Nat :=
  match e.cells[c]? with
  | some (.TypeVar c') => canonCell e c'
  | _                  => c
partial def canonDCell (e : Env) (c : Nat) : Nat :=
  match e.dcells[c]? with
  | some (.DVar c') => canonDCell e c'
  | _               => c

/-- Resolve a `ListView cell offset` to a concrete `ListSh` (positions from `offset`). -/
def viewList (e : Env) (c off : Nat) : TermShape :=
  match e.cells[canonCell e c]? with
  | some (.ListSh ps r) => .ListSh (ps.drop off) r
  | _                   => .ListSh [] .Anything

/-- Resolve a `FieldsOf cell offset` to a concrete `List Data` `ListSh` (fields from `offset`). -/
def viewFields (e : Env) (c off : Nat) : TermShape :=
  match e.dcells[canonDCell e c]? with
  | some (.DConstr _ fs r) =>
      let tail :=
        match r with
        | .DNone    => .Nothing
        | .DUnknown => .Anything
        | r'        => .DataSh r'
      .ListSh ((fs.drop off).map (.DataSh ·)) tail
  | _ => .ListSh [] (.DataSh .DUnknown)

/-! ## Lattice operations: `meet` (refine) and `join` (merge branches) -/

mutual

/-- Greatest lower bound: refine two demands on the *same* value, threading discovered structure
    through shared `Env` cells. Unknowns (`Anything`, `TypeVar`) defer to the other side;
    incompatible *concrete* shapes meet to `Nothing` (⊥), the provable-crash signal that surfaces
    as `"Nothing"`. Contravariant on function inputs (inputs `join`, outputs `meet`). -/
partial def meet (e : Env) (a b : TermShape) : TermShape × Env :=
  match e.resolve a, e.resolve b with
  | .Anything, y            => (y, e)
  | x, .Anything            => (x, e)
  | .Nothing, _             => (.Nothing, e)
  | _, .Nothing             => (.Nothing, e)
  | .TypeVar x, .TypeVar y  =>
      if x == y then (.TypeVar x, e)
      else
        let (hi, lo) := if x < y then (y, x) else (x, y)
        (.TypeVar lo, e.setCell hi (.TypeVar lo))
  | .TypeVar x, y           => (y, bindCell e x y)
  | x, .TypeVar y           => (x, bindCell e y x)
  | .Rec x, .Rec y          => if x == y then (.Rec x, e) else (.Anything, e)
  | .Rec x, y               => meet e (unfoldRec (.Rec x)) y
  | x, .Rec y               => meet e x (unfoldRec (.Rec y))
  | .Alternatives xs, y     =>
      let (rs, e') := meetEachL e xs y
      (mkAlt rs, e')
  | x, .Alternatives ys     =>
      let (rs, e') := meetEachL e ys x
      (mkAlt rs, e')
  | .Function i1 o1, .Function i2 o2 =>
      let (i, e1) := join e i1 i2          -- contravariant: demanded input is the union
      let (o, e2) := meet e1 o1 o2
      (.Function i o, e2)
  | .Delay d1, .Delay d2    =>
      let (d, e1) := meet e d1 d2
      (.Delay d, e1)
  | .PairSh a1 b1, .PairSh a2 b2 =>
      let (x, e1) := meet e a1 a2
      let (y, e2) := meet e1 b1 b2
      (.PairSh x y, e2)
  | .ListSh p1 r1, .ListSh p2 r2 =>
      meetList e p1 r1 p2 r2
  | .Constr t1 f1, .Constr t2 f2 =>
      match t1, t2 with
      | some i, some j =>
          if i == j
            then
              let (fs, e') := meetZip e f1 f2
              (.Constr (some i) fs, e')
            else (.Nothing, e)                         -- same-path, incompatible tags ⇒ ⊥
      | _, _ =>
          let (fs, e') := meetZip e f1 f2
          (.Constr (t1.orElse (λ _ => t2)) fs, e')
  | .DataSh d1, .DataSh d2  =>
      let (d, e1) := meetD e d1 d2
      (.DataSh d, e1)
  -- growable views resolve to their concrete list before meeting (positional head/tail
  -- destructuring is handled earlier in `inferProjection`, before any `meet`)
  | .ListView c off, y => meet e (viewList e c off) y
  | x, .ListView c off => meet e x (viewList e c off)
  | .FieldsOf c off, y => meet e (viewFields e c off) y
  | x, .FieldsOf c off => meet e x (viewFields e c off)
  | .ConIntTag o1, .ConIntTag o2 => (if o1 == o2 then .ConIntTag o1 else .ConInteger, e)
  | .ConIntTag o, .ConInteger | .ConInteger, .ConIntTag o => (.ConIntTag o, e)
  | .BoolPred o1 t1, .BoolPred o2 t2 => (if o1 == o2 && t1 == t2 then .BoolPred o1 t1 else .ConBool, e)
  | .BoolPred o t, .ConBool | .ConBool, .BoolPred o t => (.BoolPred o t, e)
  | x, y                    => if x == y then (x, e) else (.Nothing, e)  -- concrete clash ⇒ ⊥

/-- Least upper bound: merge the results (and per-variable demands) of alternative branches.
    `Anything` (⊤) absorbs, `Nothing` (⊥) is the unit, and incompatible concrete shapes widen to
    a union via `mkAlt` (never to `Nothing`). Dual variance to `meet` on function inputs. -/
partial def join (e : Env) (a b : TermShape) : TermShape × Env :=
  match e.resolve a, e.resolve b with
  | .Nothing, y             => (y, e)
  | x, .Nothing             => (x, e)
  | .Anything, _            => (.Anything, e)
  | _, .Anything            => (.Anything, e)
  | .Rec x, .Rec y          => if x == y then (.Rec x, e) else (.Anything, e)
  | .Rec x, y               => join e (unfoldRec (.Rec x)) y
  | x, .Rec y               => join e x (unfoldRec (.Rec y))
  | .TypeVar x, .TypeVar y  => if x == y then (.TypeVar x, e) else (mkAlt [.TypeVar x, .TypeVar y], e)
  | .Function i1 o1, .Function i2 o2 =>
      let (i, e1) := meet e i1 i2           -- dual variance
      let (o, e2) := join e1 o1 o2
      (.Function i o, e2)
  | .Delay d1, .Delay d2    =>
      let (d, e1) := join e d1 d2
      (.Delay d, e1)
  | .PairSh a1 b1, .PairSh a2 b2 =>
      let (x, e1) := join e a1 a2
      let (y, e2) := join e1 b1 b2
      (.PairSh x y, e2)
  | .ListSh p1 r1, .ListSh p2 r2 =>
      joinList e p1 r1 p2 r2
  | .Constr (some i) f1, .Constr (some j) f2 =>
      if i == j then
        let (fs, e') := joinZip e f1 f2
        (.Constr (some i) fs, e')
      else (mkAlt [.Constr (some i) f1, .Constr (some j) f2], e)
  | .Constr _ f1, .Constr _ f2 =>
      let (fs, e') := joinZip e f1 f2
      (.Constr none fs, e')
  | .DataSh d1, .DataSh d2  =>
      let (d, e1) := joinD e d1 d2
      (.DataSh d, e1)
  | .ListView c off, y => join e (viewList e c off) y
  | x, .ListView c off => join e x (viewList e c off)
  | .FieldsOf c off, y => join e (viewFields e c off) y
  | x, .FieldsOf c off => join e x (viewFields e c off)
  | .ConIntTag o1, .ConIntTag o2 => (if o1 == o2 then .ConIntTag o1 else .ConInteger, e)
  | .ConIntTag _, .ConInteger | .ConInteger, .ConIntTag _ => (.ConInteger, e)
  | .BoolPred o1 t1, .BoolPred o2 t2 => (if o1 == o2 && t1 == t2 then .BoolPred o1 t1 else .ConBool, e)
  | .BoolPred _ _, .ConBool | .ConBool, .BoolPred _ _ => (.ConBool, e)
  | x, y                    => if x == y then (x, e) else (mkAlt [x, y], e)

partial def meetEachL (e : Env) (xs : List TermShape) (other : TermShape) : List TermShape × Env :=
  match xs with
  | []      => ([], e)
  | x :: rest =>
      let (r, e1)  := meet e x other
      let (rs, e2) := meetEachL e1 rest other
      (r :: rs, e2)

partial def meetZip (e : Env) (xs ys : List TermShape) : List TermShape × Env :=
  match xs, ys with
  | x :: xs, y :: ys =>
      let (r, e1)  := meet e x y
      let (rs, e2) := meetZip e1 xs ys
      (r :: rs, e2)
  | rest, [] => (rest, e)
  | [], rest => (rest, e)

partial def joinZip (e : Env) (xs ys : List TermShape) : List TermShape × Env :=
  match xs, ys with
  | x :: xs, y :: ys =>
      let (r, e1)  := join e x y
      let (rs, e2) := joinZip e1 xs ys
      (r :: rs, e2)
  | rest, [] => (rest, e)
  | [], rest => (rest, e)

/-- Positional list refinement.  Align known positions, extra positions meet the other's
    `rest`, and the tails meet. -/
partial def meetList (e : Env) (p1 : List TermShape) (r1 : TermShape)
    (p2 : List TermShape) (r2 : TermShape) : TermShape × Env :=
  match p1, p2 with
  | x :: xs, y :: ys =>
      let (m, e1) := meet e x y
      match meetList e1 xs r1 ys r2 with
      | (.ListSh ps r, e2) => (.ListSh (m :: ps) r, e2)
      | (other, e2)        => (other, e2)
  | x :: xs, [] =>
      let (m, e1) := meet e x r2
      match meetList e1 xs r1 [] r2 with
      | (.ListSh ps r, e2) => (.ListSh (m :: ps) r, e2)
      | (other, e2)        => (other, e2)
  | [], y :: ys =>
      let (m, e1) := meet e r1 y
      match meetList e1 [] r1 ys r2 with
      | (.ListSh ps r, e2) => (.ListSh (m :: ps) r, e2)
      | (other, e2)        => (other, e2)
  | [], [] =>
      let (r, e1) := meet e r1 r2
      (.ListSh [] r, e1)

partial def joinList (e : Env) (p1 : List TermShape) (r1 : TermShape)
    (p2 : List TermShape) (r2 : TermShape) : TermShape × Env :=
  match p1, p2 with
  | x :: xs, y :: ys =>
      let (m, e1) := join e x y
      match joinList e1 xs r1 ys r2 with
      | (.ListSh ps r, e2) => (.ListSh (m :: ps) r, e2)
      | (other, e2)        => (other, e2)
  | x :: xs, [] =>
      let (m, e1) := join e x r2
      match joinList e1 xs r1 [] r2 with
      | (.ListSh ps r, e2) => (.ListSh (m :: ps) r, e2)
      | (other, e2)        => (other, e2)
  | [], y :: ys =>
      let (m, e1) := join e r1 y
      match joinList e1 [] r1 ys r2 with
      | (.ListSh ps r, e2) => (.ListSh (m :: ps) r, e2)
      | (other, e2)        => (other, e2)
  | [], [] =>
      let (r, e1) := join e r1 r2
      (.ListSh [] r, e1)

partial def meetD (e : Env) (a b : DataShape) : DataShape × Env :=
  match e.resolveD a, e.resolveD b with
  | .DUnknown, y => (y, e)
  | x, .DUnknown => (x, e)
  | .DNone, _    => (.DNone, e)
  | _, .DNone    => (.DNone, e)
  | .DVar x, .DVar y =>
      if x == y then (.DVar x, e)
      else
        let (hi, lo) := if x < y then (y, x) else (x, y)
        (.DVar lo, e.setDCell hi (.DVar lo))
  | .DVar x, y   => (y, bindDCell e x y)
  | x, .DVar y   => (x, bindDCell e y x)
  | .DRec x, .DRec y => if x == y then (.DRec x, e) else (.DUnknown, e)
  | .DRec x, y   => meetD e (unfoldDRec (.DRec x)) y
  | x, .DRec y   => meetD e x (unfoldDRec (.DRec y))
  | .DConstr t1 f1 r1, .DConstr t2 f2 r2 =>
      match t1, t2 with
      | some i, some j =>
          if i == j then
            let (fs, e1) := meetDZip e f1 f2
            let (r, e2) := meetD e1 r1 r2
            (.DConstr (some i) fs r, e2)
          else (.DNone, e)
      | _, _ =>
          let (fs, e1) := meetDZip e f1 f2
          let (r, e2) := meetD e1 r1 r2
          (.DConstr (t1.orElse (λ _ => t2)) fs r, e2)
  | .DMap k1 v1, .DMap k2 v2 =>
      let (k, e1) := meetD e k1 k2
      let (v, e2) := meetD e1 v1 v2
      (.DMap k v, e2)
  | .DList e1', .DList e2' =>
      let (el, e1) := meetD e e1' e2'
      (.DList el, e1)
  | x, y => if x == y then (x, e) else (.DNone, e)

partial def joinD (e : Env) (a b : DataShape) : DataShape × Env :=
  match e.resolveD a, e.resolveD b with
  | .DNone, y => (y, e)
  | x, .DNone => (x, e)
  | .DUnknown, _ => (.DUnknown, e)
  | _, .DUnknown => (.DUnknown, e)
  | .DRec x, .DRec y => if x == y then (.DRec x, e) else (.DUnknown, e)
  | .DRec x, y   => joinD e (unfoldDRec (.DRec x)) y
  | x, .DRec y   => joinD e x (unfoldDRec (.DRec y))
  | .DConstr (some i) f1 r1, .DConstr (some j) f2 r2 =>
      if i == j then
        let (fs, e1) := joinDZip e f1 f2
        let (r, e2) := joinD e1 r1 r2
        (.DConstr (some i) fs r, e2)
      else (mkAltD [.DConstr (some i) f1 r1, .DConstr (some j) f2 r2], e)
  | .DMap k1 v1, .DMap k2 v2 =>
      let (k, e1) := joinD e k1 k2
      let (v, e2) := joinD e1 v1 v2
      (.DMap k v, e2)
  | .DList e1', .DList e2' =>
      let (el, e1) := joinD e e1' e2'
      (.DList el, e1)
  | x, y => if x == y then (x, e) else (mkAltD [x, y], e)

partial def meetDZip (e : Env) (xs ys : List DataShape) : List DataShape × Env :=
  match xs, ys with
  | x :: xs, y :: ys =>
      let (r, e1) := meetD e x y
      let (rs, e2) := meetDZip e1 xs ys
      (r :: rs, e2)
  | rest, [] => (rest, e)
  | [], rest => (rest, e)

partial def joinDZip (e : Env) (xs ys : List DataShape) : List DataShape × Env :=
  match xs, ys with
  | x :: xs, y :: ys =>
      let (r, e1) := joinD e x y
      let (rs, e2) := joinDZip e1 xs ys
      (r :: rs, e2)
  | rest, [] => (rest, e)
  | [], rest => (rest, e)

end

def joinAll (e : Env) : List TermShape → TermShape × Env
  | []      => (.Nothing, e)
  | s :: ss => ss.foldl (λ (acc, e) x => join e acc x) (s, e)

/-! ## Growable positional list / `Data.Constr` views (heterogeneous by default) -/

/-- Cap on discovered positions; beyond it the tail stays homogeneous (recursion fallback). -/
def maxPositions : Nat := 32

/-- Allocate `n` fresh term-shape cells. -/
def freshTermCells (e : Env) : Nat → List TermShape × Env
  | 0     => ([], e)
  | k + 1 => let (c, e1) := e.fresh; let (cs, e2) := freshTermCells e1 k; (c :: cs, e2)

def freshDataCells (e : Env) : Nat → List DataShape × Env
  | 0     => ([], e)
  | k + 1 => let (c, e1) := e.freshD; let (cs, e2) := freshDataCells e1 k; (c :: cs, e2)

/-- Grow the `ListSh` in `cells[cell]` so position `offset` exists, returning it (fresh cells
    for new positions ⇒ per-position refinement; capped, leaving an open homogeneous tail). -/
partial def growList (e : Env) (cell offset : Nat) : TermShape × Env :=
  let cell := canonCell e cell
  let (ps, r) :=
    match e.cells[cell]? with
    | some (.ListSh ps r) => (ps, r)
    | _                   => ([], .Anything)
  if h : offset < ps.length then (ps[offset], e)
  else if offset ≥ maxPositions then (r, e)
  else
    let (newCells, e1) := freshTermCells e (offset + 1 - ps.length)
    let newPs := ps ++ newCells
    let e2 := e1.setCell cell (.ListSh newPs r)
    (newPs[offset]!, e2)

/-- Grow the `DConstr` in `dcells[cell]` so field `offset` exists, returning it. -/
partial def growFields (e : Env) (cell offset : Nat) : DataShape × Env :=
  let cell := canonDCell e cell
  let (tag, fs, r) := match e.dcells[cell]? with
    | some (.DConstr t f rr) => (t, f, rr)
    | _                      => (none, [], .DUnknown)
  if h : offset < fs.length then (fs[offset], e)
  else if offset ≥ maxPositions then (r, e)
  else
    let (newCells, e1) := freshDataCells e (offset + 1 - fs.length)
    let newFs := fs ++ newCells
    let e2 := e1.setDCell cell (.DConstr tag newFs r)
    (newFs[offset]!, e2)

/-! ## Literal `Data` / `Const` → shape -/

def intToNat (i : Integer) : Nat := Int.toNat i

partial def dataToShape : Data → DataShape
  | .Constr i fields => .DConstr (some (intToNat i)) (fields.map dataToShape) .DNone
  | .Map _           => .DMap .DUnknown .DUnknown
  | .List _          => .DList .DUnknown
  | .I _             => .DInt
  | .B _             => .DBytes

partial def constToShape : Const → TermShape
  | .Integer _              => .ConInteger
  | .ByteString _           => .ConByteString
  | .String _               => .ConString
  | .Unit                   => .ConUnit
  | .Bool _                 => .ConBool
  | .ConstList cs           => .ListSh (cs.map constToShape) .Nothing
  | .ConstDataList ds       => .ListSh (ds.map (λ d => .DataSh (dataToShape d))) .Nothing
  | .ConstPairDataList ps   => .ListSh (ps.map (λ (a, b) => .PairSh (.DataSh (dataToShape a)) (.DataSh (dataToShape b)))) .Nothing
  | .Pair (a, b)            => .PairSh (constToShape a) (constToShape b)
  | .PairData (a, b)        => .PairSh (.DataSh (dataToShape a)) (.DataSh (dataToShape b))
  | .Data d                 => .DataSh (dataToShape d)
  | .Bls12_381_G1_element _ => .ConBls12_381_G1_element
  | .Bls12_381_G2_element _ => .ConBls12_381_G2_element
  | .Bls12_381_MlResult _   => .ConBls12_381_MlResult

/-! ## Builtin shapes (structural, with linking cells) -/

open BuiltinFun in
/-- The (Delay-wrapped where UPLC-forced) arrow shape of a builtin, with fresh refinement
    cells linking inputs to outputs so `meet` performs structural discovery. -/
def shapeOfBuiltin (e : Env) : BuiltinFun → TermShape × Env
  | AddInteger | SubtractInteger | MultiplyInteger
  | DivideInteger | QuotientInteger | RemainderInteger | ModInteger =>
      (.Function .ConInteger (.Function .ConInteger .ConInteger), e)
  | EqualsInteger | LessThanInteger | LessThanEqualsInteger =>
      (.Function .ConInteger (.Function .ConInteger .ConBool), e)
  | ExpModInteger =>
      (.Function .ConInteger (.Function .ConInteger (.Function .ConInteger .ConInteger)), e)
  | AppendByteString =>
      (.Function .ConByteString (.Function .ConByteString .ConByteString), e)
  | ConsByteString =>
      (.Function .ConInteger (.Function .ConByteString .ConByteString), e)
  | SliceByteString =>
      (.Function .ConInteger (.Function .ConInteger (.Function .ConByteString .ConByteString)), e)
  | LengthOfByteString =>
      (.Function .ConByteString .ConInteger, e)
  | IndexByteString =>
      (.Function .ConByteString (.Function .ConInteger .ConInteger), e)
  | EqualsByteString | LessThanByteString | LessThanEqualsByteString =>
      (.Function .ConByteString (.Function .ConByteString .ConBool), e)
  | Sha2_256 | Sha3_256 | Blake2b_256 | Keccak_256 | Blake2b_224 | Ripemd_160 =>
      (.Function .ConByteString .ConByteString, e)
  | VerifyEd25519Signature | VerifyEcdsaSecp256k1Signature | VerifySchnorrSecp256k1Signature =>
      (.Function .ConByteString (.Function .ConByteString (.Function .ConByteString .ConBool)), e)
  | IntegerToByteString =>
      (.Function .ConBool (.Function .ConInteger (.Function .ConInteger .ConByteString)), e)
  | ByteStringToInteger =>
      (.Function .ConBool (.Function .ConByteString .ConInteger), e)
  | AppendString =>
      (.Function .ConString (.Function .ConString .ConString), e)
  | EqualsString =>
      (.Function .ConString (.Function .ConString .ConBool), e)
  | EncodeUtf8 =>
      (.Function .ConString .ConByteString, e)
  | DecodeUtf8 =>
      (.Function .ConByteString .ConString, e)
  -- choose / if (branch-polymorphic).  Bare shapes for partial application / display;
  -- the fully-applied path (`inferChoose`) fork-joins the branches for precise unions.
  | IfThenElse =>
      let (a, e') := e.fresh
      (.Delay (.Function .ConBool (.Function a (.Function a a))), e')
  | ChooseUnit =>
      let (a, e') := e.fresh
      (.Delay (.Function .ConUnit (.Function a a)), e')
  | Trace =>
      let (a, e') := e.fresh
      (.Delay (.Function .ConString (.Function a a)), e')
  | FstPair =>
      let (a, e1) := e.fresh
      let (b, e2) := e1.fresh
      (.Delay (.Delay (.Function (.PairSh a b) a)), e2)
  | SndPair =>
      let (a, e1) := e.fresh
      let (b, e2) := e1.fresh
      (.Delay (.Delay (.Function (.PairSh a b) b)), e2)
  | ChooseList =>
      let (el, e1) := e.fresh
      let (r, e2) := e1.fresh
      (.Delay (.Delay (.Function (.ListSh [] el) (.Function r (.Function r r)))), e2)
  | MkCons =>
      let (a, e') := e.fresh
      (.Delay (.Function a (.Function (.ListSh [] a) (.ListSh [] a))), e')
  | HeadList =>
      let (a, e') := e.fresh
      (.Delay (.Function (.ListSh [] a) a), e')
  | TailList =>
      let (a, e') := e.fresh
      (.Delay (.Function (.ListSh [] a) (.ListSh [] a)), e')
  | NullList =>
      let (a, e') := e.fresh
      (.Delay (.Function (.ListSh [] a) .ConBool), e')
  | DropList =>
      let (a, e') := e.fresh
      (.Delay (.Function .ConInteger (.Function (.ListSh [] a) (.ListSh [] a))), e')
  | ChooseData =>
      let (r, e') := e.fresh
      (.Delay (.Function (.DataSh .DUnknown)
        (.Function r (.Function r (.Function r (.Function r (.Function r r)))))), e')
  | ConstrData =>
      (.Function .ConInteger (.Function (.ListSh [] (.DataSh .DUnknown)) (.DataSh (.DConstr none [] .DUnknown))), e)
  | MapData =>
      (.Function (.ListSh [] (.PairSh (.DataSh .DUnknown) (.DataSh .DUnknown))) (.DataSh (.DMap .DUnknown .DUnknown)), e)
  | ListData =>
      (.Function (.ListSh [] (.DataSh .DUnknown)) (.DataSh (.DList .DUnknown)), e)
  | IData =>
      (.Function .ConInteger (.DataSh .DInt), e)
  | BData =>
      (.Function .ConByteString (.DataSh .DBytes), e)
  | UnConstrData =>
      let (k, e') := e.freshD
      (.Function (.DataSh (.DConstr none [] k))
                 (.PairSh .ConInteger (.ListSh [] (.DataSh k))), e')
  | UnMapData =>
      let (k, e1) := e.freshD
      let (v, e2) := e1.freshD
      (.Function (.DataSh (.DMap k v))
                 (.ListSh [] (.PairSh (.DataSh k) (.DataSh v))), e2)
  | UnListData =>
      let (k, e') := e.freshD
      (.Function (.DataSh (.DList k)) (.ListSh [] (.DataSh k)), e')
  | UnIData =>
      (.Function (.DataSh .DInt) .ConInteger, e)
  | UnBData =>
      (.Function (.DataSh .DBytes) .ConByteString, e)
  | EqualsData =>
      (.Function (.DataSh .DUnknown) (.Function (.DataSh .DUnknown) .ConBool), e)
  | MkPairData =>
      (.Function (.DataSh .DUnknown) (.Function (.DataSh .DUnknown)
        (.PairSh (.DataSh .DUnknown) (.DataSh .DUnknown))), e)
  | MkNilData =>
      (.Function .ConUnit (.ListSh [] (.DataSh .DUnknown)), e)
  | MkNilPairData =>
      (.Function .ConUnit (.ListSh [] (.PairSh (.DataSh .DUnknown) (.DataSh .DUnknown))), e)
  | SerializeData =>
      (.Function (.DataSh .DUnknown) .ConByteString, e)
  | Bls12_381_G1_add =>
      (.Function .ConBls12_381_G1_element (.Function .ConBls12_381_G1_element .ConBls12_381_G1_element), e)
  | Bls12_381_G1_neg =>
      (.Function .ConBls12_381_G1_element .ConBls12_381_G1_element, e)
  | Bls12_381_G1_scalarMul =>
      (.Function .ConInteger (.Function .ConBls12_381_G1_element .ConBls12_381_G1_element), e)
  | Bls12_381_G1_equal =>
      (.Function .ConBls12_381_G1_element (.Function .ConBls12_381_G1_element .ConBool), e)
  | Bls12_381_G1_hashToGroup =>
      (.Function .ConByteString (.Function .ConByteString .ConBls12_381_G1_element), e)
  | Bls12_381_G1_compress =>
      (.Function .ConBls12_381_G1_element .ConByteString, e)
  | Bls12_381_G1_uncompress =>
      (.Function .ConByteString .ConBls12_381_G1_element, e)
  | Bls12_381_G1_multiScalarMul =>
      (.Function (.ListSh [] .Anything) (.Function (.ListSh [] .Anything) .ConBls12_381_G1_element), e)
  | Bls12_381_G2_add =>
      (.Function .ConBls12_381_G2_element (.Function .ConBls12_381_G2_element .ConBls12_381_G2_element), e)
  | Bls12_381_G2_neg =>
      (.Function .ConBls12_381_G2_element .ConBls12_381_G2_element, e)
  | Bls12_381_G2_scalarMul =>
      (.Function .ConInteger (.Function .ConBls12_381_G2_element .ConBls12_381_G2_element), e)
  | Bls12_381_G2_equal =>
      (.Function .ConBls12_381_G2_element (.Function .ConBls12_381_G2_element .ConBool), e)
  | Bls12_381_G2_hashToGroup =>
      (.Function .ConByteString (.Function .ConByteString .ConBls12_381_G2_element), e)
  | Bls12_381_G2_compress =>
      (.Function .ConBls12_381_G2_element .ConByteString, e)
  | Bls12_381_G2_uncompress =>
      (.Function .ConByteString .ConBls12_381_G2_element, e)
  | Bls12_381_G2_multiScalarMul =>
      (.Function (.ListSh [] .Anything) (.Function (.ListSh [] .Anything) .ConBls12_381_G2_element), e)
  | Bls12_381_millerLoop =>
      (.Function .ConBls12_381_G1_element (.Function .ConBls12_381_G2_element .ConBls12_381_MlResult), e)
  | Bls12_381_mulMlResult =>
      (.Function .ConBls12_381_MlResult (.Function .ConBls12_381_MlResult .ConBls12_381_MlResult), e)
  | Bls12_381_finalVerify =>
      (.Function .ConBls12_381_MlResult (.Function .ConBls12_381_MlResult .ConBool), e)
  | AndByteString | OrByteString | XorByteString =>
      (.Function .ConBool (.Function .ConByteString (.Function .ConByteString .ConByteString)), e)
  | ComplementByteString =>
      (.Function .ConByteString .ConByteString, e)
  | ReadBit =>
      (.Function .ConByteString (.Function .ConInteger .ConBool), e)
  | WriteBits =>
      (.Function .ConByteString (.Function (.ListSh [] .Anything) (.Function .ConBool .ConByteString)), e)
  | ReplicateByte =>
      (.Function .ConInteger (.Function .ConInteger .ConByteString), e)
  | ShiftByteString | RotateByteString =>
      (.Function .ConByteString (.Function .ConInteger .ConByteString), e)
  | CountSetBits | FindFirstSetBit =>
      (.Function .ConByteString .ConInteger, e)

/-- Choose/if builtins and their `(#discriminants, #branches)` shape. -/
def chooseArity : BuiltinFun → Option (Nat × Nat)
  | .IfThenElse => some (1, 2)
  | .ChooseUnit => some (1, 1)
  | .Trace      => some (1, 1)
  | .ChooseList => some (1, 2)
  | .ChooseData => some (1, 5)
  | _           => none

def discDemands : BuiltinFun → List TermShape
  | .IfThenElse => [.ConBool]
  | .ChooseUnit => [.ConUnit]
  | .Trace      => [.ConString]
  | .ChooseList => [.ListSh [] .Anything]
  | .ChooseData => [.DataSh .DUnknown]
  | _           => []

/-! ## Inference engine -/

/-- An unapplied function branch cannot honestly be reported as the `Case` result. -/
def caseBranchResult : TermShape → TermShape
  | .Function _ _ => .Anything
  | other         => other

/-- Peel an application spine: `f a b c` → `(f, [a,b,c])`. -/
partial def collectApp : Term → Term × List Term
  | .Apply f a => let (h, args) := collectApp f; (h, args ++ [a])
  | t          => (t, [])

/-- Peel leading `Force`s. -/
partial def peelForce : Term → Nat × Term
  | .Force t => let (k, t') := peelForce t; (k + 1, t')
  | t        => (0, t)

/-- Does `body` mention the free variable `name` (respecting shadowing)? -/
partial def mentions (name : String) : Term → Bool
  | .Var n       => n == name
  | .Lam n b     => n != name && mentions name b
  | .Apply f a   => mentions name f || mentions name a
  | .Delay t     => mentions name t
  | .Force t     => mentions name t
  | .Constr _ fs => fs.any (mentions name)
  | .Case s bs   => mentions name s || bs.any (mentions name)
  | _            => false

/-- Heuristic detection of self-application (the Z/Y-combinator recursion encoding):
    `name` applied to a term that itself mentions `name`. -/
partial def selfApplied (name : String) : Term → Bool
  | .Apply (.Var n) a => (n == name && mentions name a) || selfApplied name a
  | .Apply f a        => selfApplied name f || selfApplied name a
  | .Lam n b          => n != name && selfApplied name b
  | .Delay t          => selfApplied name t
  | .Force t          => selfApplied name t
  | .Constr _ fs      => fs.any (selfApplied name)
  | .Case s bs        => selfApplied name s || bs.any (selfApplied name)
  | _                 => false

/-- Peel a function shape into its argument shapes and final result. -/
partial def peelArrows (e : Env) (s : TermShape) : List TermShape × TermShape :=
  match e.resolve s with
  | .Function i o => let (ins, ret) := peelArrows e o; (i :: ins, ret)
  | other         => ([], other)

/-- A branch that always errors/diverges (its shape is `Nothing`, under any `Delay`s). -/
partial def isDeadBranch (e : Env) (s : TermShape) : Bool :=
  match e.resolve s with
  | .Nothing => true
  | .Delay d => isDeadBranch e d
  | _        => false

/-- Tactic 2: narrow a `chooseData` discriminant to the variants of its *live* branches
    (branch order: Constr, Map, List, I, B). Dead (`Error`) branches rule out variants. -/
partial def narrowChooseData (e : Env) (discArgs : List Term) (branchShapes : List TermShape) : Env :=
  let variants : List DataShape :=
    [.DConstr none [] .DUnknown, .DMap .DUnknown .DUnknown, .DList .DUnknown, .DInt, .DBytes]
  let live := (variants.zip branchShapes).filterMap
    (λ (v, s) => if isDeadBranch e s then none else some v)
  let narrowed := if live.length ≥ 5 then .DUnknown else mkAltD live
  match discArgs with
  | (.Var vn) :: _ =>
      let (r, e') := meet e (e.getVar vn) (.DataSh narrowed)
      e'.setVar vn r
  | _ => e

mutual

/-- Core inference: from the current `Env`, compute a term's shape and the updated `Env`
    (threaded refinement cells and per-variable demands). Dispatches on the term — constants and
    builtins get their literal/arrow shapes, `Lam` binds its parameter and (for a recursive
    binder) runs the fuelled fixpoint `fixLam`, and application spines route to the tactic
    helpers (`inferBetaRedex`, `inferProjection`, `inferUnConstr`, `inferEqualsInteger`,
    `inferIfThenElse`, `inferChoose`) before falling back to plain `applyOne`. -/
partial def infer (e : Env) : Term → TermShape × Env
  | .Var name    => (e.getVar name, e)
  | .Const c     => (constToShape c, e)
  | .Builtin b   => shapeOfBuiltin e b
  | .Error       => (.Nothing, e)
  | .Delay t     => let (s, e') := infer e t; (.Delay s, e')
  | .Force t     =>
      match infer e t with
      | (.Delay d  , e') => (d, e')
      | (.Anything , e') => (.Anything, e')
      | (.TypeVar n, e') => let (out, e'') := e'.fresh; (out, e''.setCell n (.Delay out))
      | (_         , e') => (.Nothing, e')
  | .Lam name body =>
      let prior := e.vars[name]?
      let (argShape, bShape, e1) :=
        if e.fuel > 0 && selfApplied name body then
          -- recursive binder: solve its demand by fuel-bounded iteration
          fixLam { e with fuel := e.fuel - 1 } name body (min e.fuel 3) .Anything
        else
          let (bs, e') := infer (e.setVar name .Anything) body
          (e'.getVar name, bs, e')
      let restored := match prior with
        | some p => e1.setVar name p
        | none   => e1.eraseVar name
      (.Function (zonk e1 argShape) (zonk e1 bShape), restored)
  | .Constr idx fields =>
      let (fieldShapes, e') := inferList e fields
      (.Constr (some idx) fieldShapes, e')
  | .Apply f a =>
      let (head, args) := collectApp (.Apply f a)
      match head with
      -- beta-redex: analyse context-sensitively by binding parameters to actual arguments
      -- (their shapes share refinement cells, so structure discovered inside the body flows
      -- back to the argument). Compiled UPLC is largely such redexes (encoded `let`s).
      | .Lam _ _ => inferBetaRedex e head args
      -- tactic 3: a variable bound to a lambda is unrolled (bounded) at its call site, so
      -- recursive calls (Z/Y-combinator `self`) are inlined a few levels deep
      | .Var fn =>
          match e.funDefs[fn]? with
          | some lam =>
              if e.unrollFuel > 0 then inferBetaRedex { e with unrollFuel := e.unrollFuel - 1 } lam args
              else applyOne e f a
          | none => applyOne e f a
      | _ =>
        let (_, core) := peelForce head
        match core with
        | .Builtin b =>
            match b with
            -- tactic 4: positional list projections
            | .HeadList | .TailList =>
                match args with
                | listArg :: rest => let (r, e') := inferProjection e b listArg; applyArgs e' r rest
                | []              => applyOne e f a
            -- tactic 1: tag reconstruction
            | .UnConstrData =>
                match args with
                | dArg :: rest => let (r, e') := inferUnConstr e dArg; applyArgs e' r rest
                | []           => applyOne e f a
            | .EqualsInteger =>
                match args with
                | a1 :: a2 :: rest => let (r, e') := inferEqualsInteger e a1 a2; applyArgs e' r rest
                | _                => applyOne e f a
            | .IfThenElse =>
                match args with
                | cond :: thenB :: elseB :: rest => inferIfThenElse e cond thenB elseB rest
                | _                              => applyOne e f a
            | _ =>
                -- choose/if fork-join when the spine head is a fully-applied choose builtin
                match chooseArity b with
                | some (d, nb) =>
                    if args.length ≥ d + nb then inferChoose e b d nb args
                    else applyOne e f a
                | none => applyOne e f a
        | _ => applyOne e f a
  | .Case scrut branches =>
      inferCase e scrut branches

/-- Context-sensitive analysis of a beta-redex spine `(λp₀. λp₁. … body) a₀ a₁ …`: bind each
    parameter to the *actual* argument's shape (which shares refinement cells), then analyse the
    body in that context. Leftover args (beyond the lambdas) are applied normally. -/
partial def inferBetaRedex (e : Env) : Term → List Term → TermShape × Env
  | .Lam name body, arg :: rest =>
      let (argShape, e1) := infer e arg
      let prior    := e1.vars[name]?
      let priorFun := e1.funDefs[name]?
      -- tactic 3: track when a parameter is bound to a lambda (directly, or via another
      -- variable that is), so a recursive call through it can be unrolled
      let fd? : Option Term := match arg with
        | .Lam _ _ => some arg
        | .Var v   => e1.funDefs[v]?
        | _        => none
      let eBound := match fd? with
        | some fd => { e1 with funDefs := e1.funDefs.insert name fd }
        | none    => { e1 with funDefs := e1.funDefs.erase name }
      let (r, e2) := inferBetaRedex (eBound.setVar name argShape) body rest
      let e3 := match prior with
                | some p => e2.setVar name p
                | none   => e2.eraseVar name
      let fd := match priorFun with
                | some p => e3.funDefs.insert name p
                | none   => e3.funDefs.erase name
      let e4 := { e3 with funDefs := fd }
      (r, e4)
  | fn, args =>
      let (fnShape, e1) := infer e fn
      applyArgs e1 fnShape args

/-- Ordinary (non-choose) single application `f a`, ported from the original three-way split,
    using `meet`. -/
partial def applyOne (e : Env) (f a : Term) : TermShape × Env :=
  match f with
  | .Var fname =>
      let (argShape, e1) := infer e a
      match e1.resolve (e1.getVar fname) with
      | .Function input output =>
          let (refined, e2) := meet e1 input argShape
          if refined == .Nothing then (.Nothing, e2)
          else
            let e3 := e2.setVar fname (.Function refined output)
            let e4 := match a with
                      | .Var an => e3.setVar an refined
                      | _       => e3
            (e4.resolve output, e4)
      | .Anything | .TypeVar _ =>
          let (out, e2) := e1.fresh
          (out, e2.setVar fname (.Function argShape out))
      | _ => (.Nothing, e1)
  | _ =>
      let (fnShape, e1) := infer e f
      let (argShape, e2) := infer e1 a
      match e2.resolve fnShape with
      | .Function input output =>
          let (refined, e3) := meet e2 input argShape
          if refined == .Nothing then (.Nothing, e3)
          else
            let e4 := match a with
                      | .Var an => e3.setVar an refined
                      | _       => e3
            (e4.resolve output, e4)
      | .Anything => (.Anything, e2)
      | .TypeVar n =>
          let (out, e3) := e2.fresh
          (out, e3.setCell n (.Function argShape out))
      | _ => (.Nothing, e2)

/-- Apply a shape to a list of *term* arguments (for extra args after a choose builtin). -/
partial def applyArgs (e : Env) (fnShape : TermShape) : List Term → TermShape × Env
  | []        => (fnShape, e)
  | arg :: rest =>
      let (aShape, e1) := infer e arg
      match e1.resolve fnShape with
      | .Function input output =>
          let (refined, e2) := meet e1 input aShape
          if refined == .Nothing then (.Nothing, e2)
          else
            let e3 := match arg with
                      | .Var an => e2.setVar an refined
                      | _       => e2
            applyArgs e3 (e3.resolve output) rest
      | .Anything => applyArgs e1 .Anything rest
      | .TypeVar n =>
          let (out, e2) := e1.fresh
          applyArgs (e2.setCell n (.Function aShape out)) out rest
      | _ => (.Nothing, e1)

/-- Tactic 4: positional `headList`/`tailList`. Navigate the list's known positions (head =
    position 0, tail drops it) instead of meeting all positions together; refine an unknown
    list argument to `[…elem]`. -/
partial def inferProjection (e : Env) (b : BuiltinFun) (listArg : Term) : TermShape × Env :=
  let (ls0, e1) := infer e listArg
  -- navigate a growable list view: head grows position `off`, tail advances the offset
  let navView : Env → Nat → Nat → TermShape × Env := (λ e c off =>
    match b with
    | .HeadList => growList e c off
    | _         => (.ListView c (off + 1), e))
  match e1.resolve ls0 with
  | .ListView c off => navView e1 c off
  | .FieldsOf c off =>
      match b with
      | .HeadList => let (fld, e2) := growFields e1 c off; (.DataSh fld, e2)
      | _         => (.FieldsOf c (off + 1), e1)
  | .ListSh (p :: ps) rest =>                       -- concrete positional (literals)
      match b with
      | .HeadList => (e1.resolve p, e1)
      | _         => (.ListSh ps rest, e1)
  | .ListSh [] rest =>                              -- known-homogeneous: stays homogeneous
      match b with
      | .HeadList => (e1.resolve rest, e1)
      | _         => (.ListSh [] rest, e1)
  | .Anything =>                                    -- unknown list: homogeneous element cell
      let (elem, e2) := e1.fresh                    -- (shared, so a fold consumer unifies with it)
      let e3 := match listArg with | .Var n => e2.setVar n (.ListSh [] elem) | _ => e2
      match b with
      | .HeadList => (elem, e3)
      | _         => (.ListSh [] elem, e3)
  | .TypeVar n =>
      let (elem, e2) := e1.fresh
      let e3 := e2.setCell n (.ListSh [] elem)
      match b with
      | .HeadList => (elem, e3)
      | _         => (.ListSh [] elem, e3)
  | _ => (.Nothing, e1)

/-- Tactic 1: `unConstrData d`. Demand `d` a `Data.Constr`; when `d` is a variable, tag its
    integer tag with the owner so downstream `equalsInteger` guards can refine it. -/
partial def inferUnConstr (e : Env) (dArg : Term) : TermShape × Env :=
  let (dShape, e1) := infer e dArg
  -- give `d`'s Data a cell handle, and ensure that cell holds a `DConstr` (fields grown lazily)
  let c := e1.next
  let (r, e2) := meet ({ e1 with next := c + 1 }) dShape (.DataSh (.DVar c))
  let e3 := match dArg with | .Var d => e2.setVar d r | _ => e2
  let cc := canonDCell e3 c
  -- fields grow lazily & positionally; the tail is a *shared* cell, so a fold consumer's
  -- refinements flow back into `d`'s discovered shape
  let rc := e3.next
  let (_, e4) := meetD ({ e3 with next := rc + 1 }) (.DVar cc) (.DConstr none [] (.DVar rc))
  let cc := canonDCell e4 cc
  let tagShape : TermShape := match dArg with | .Var d => .ConIntTag d | _ => .ConInteger
  (.PairSh tagShape (.FieldsOf cc 0), e4)

/-- Tactic 1: `equalsInteger`. If one side is a tag (`ConIntTag`) and the other a literal `K`,
    yield the refinement predicate `BoolPred owner K`; otherwise a plain `Bool`. -/
partial def inferEqualsInteger (e : Env) (a1 a2 : Term) : TermShape × Env :=
  let (s1, e1) := infer e a1
  let (s2, e2) := infer e1 a2
  let pred : Option (String × Nat) :=
    match e2.resolve s1, a2 with
    | .ConIntTag o, .Const (.Integer k) => some (o, intToNat k)
    | _, _ =>
      match e2.resolve s2, a1 with
      | .ConIntTag o, .Const (.Integer k) => some (o, intToNat k)
      | _, _ => none
  match pred with
  | some (o, k) => (.BoolPred o k, e2)
  | none        => (.ConBool, e2)

/-- Tactic 1: path-sensitive `ifThenElse`. When the condition is a tag predicate, refine the
    owner to that tag in the then-branch; merge branch demands by join, skipping dead
    (`Error`) branches so an `else Error` fallback does not pollute the reconstructed tag set. -/
partial def inferIfThenElse (e : Env) (cond thenB elseB : Term) (extra : List Term) : TermShape × Env :=
  let (condShape, e1) := infer e cond
  let baseVars := e1.vars
  let eThen := match e1.resolve condShape with
    | .BoolPred owner k =>
        let (r, ev) := meet { e1 with vars := baseVars } (e1.getVar owner)
                            (.DataSh (.DConstr (some k) [] .DUnknown))
        ev.setVar owner r
    | _ => { e1 with vars := baseVars }
  let (sT, eT) := infer eThen thenB
  let (sE, eE) := infer { eT with vars := baseVars } elseB
  let liveEnvs := ([(sT, eT), (sE, eE)]).filterMap
    (λ (s, env) => if isDeadBranch env s then none else some env)
  let mergedVars := match liveEnvs with
    | []            => baseVars
    | first :: rest =>
        rest.foldl (λ acc env =>
          env.vars.fold (λ m k v => let (j, _) := join env (m.getD k .Anything) v; m.insert k j) acc)
          first.vars
  let (joined, e2) := join { eE with vars := mergedVars } sT sE
  applyArgs e2 joined extra

/-- Demand the discriminant arguments of a choose/if builtin (sequential meet). -/
partial def demandDiscriminants (e : Env) : List TermShape → List Term → Env
  | ty :: tys, arg :: args =>
      let (aShape, e1) := infer e arg
      let (refined, e2) := meet e1 ty aShape
      let e3 := match arg with | .Var an => e2.setVar an refined | _ => e2
      demandDiscriminants e3 tys args
  | _, _ => e

/-- Fork-join a choose/if builtin: demand discriminants, join the branches (each inferred from
    the same base env), then apply any extra args to the joined result. -/
partial def inferChoose (e : Env) (b : BuiltinFun) (d nb : Nat) (args : List Term) : TermShape × Env :=
  let e1 := demandDiscriminants e (discDemands b) (args.take d)
  let branchArgs := (args.drop d).take nb
  let extraArgs := args.drop (d + nb)
  let (branchShapes, e2) := inferBranches e1 branchArgs
  -- tactic 2: narrow a chooseData discriminant to the variants of its live branches
  let e2 := match b with
    | .ChooseData => narrowChooseData e2 (args.take d) branchShapes
    | _           => e2
  let (joined, e3) := joinAll e2 branchShapes
  applyArgs e3 joined extraArgs

/-- Infer each branch from the *same* variable environment (fork), threading cells; variable
    demands are joined across branches. -/
partial def inferBranches (base : Env) (branches : List Term) : List TermShape × Env :=
  let rec go (e : Env) (accVars : HashMap String TermShape) : List Term → List TermShape × Env
    | []      => ([], { e with vars := accVars })
    | br :: rest =>
        let (s, e') := infer { e with vars := base.vars } br
        let mergedVars := e'.vars.fold (λ acc k v =>
          let cur := acc.getD k .Anything
          let (j, _) := join e' cur v
          acc.insert k j) accVars
        let (ss, e'') := go { e' with vars := base.vars } mergedVars rest
        (s :: ss, e'')
  go base base.vars branches

partial def inferCase (e : Env) (scrut : Term) (branches : List Term) : TermShape × Env :=
  -- Literal-`Constr` scrutinee: known tag, select & apply the branch with positional refinement.
  match scrut with
  | .Constr idx fields =>
      let (branchShapes, e1) := inferList e branches
      let (fieldShapes , e2) := inferList e1 fields
      match branchShapes[idx]? with
      | some bShape =>
          let named := List.zip fields fieldShapes
          applyToFields e2 bShape named
      | none => (.Nothing, e2)
  | _ =>
      let (scrutShape  , e1) := infer e scrut
      let (branchShapes, e2) := inferList e1 branches
      match e2.resolve scrutShape with
      | .Constr (some idx) fields =>
          match branchShapes[idx]? with
          | some bShape => applyShapes e2 bShape fields
          | none        => (.Nothing, e2)
      | resolved =>
          -- Reconstruct the sum-of-products type from the eliminator: branch `i` corresponds to
          -- constructor tag `i`, and its parameter demands are constructor `i`'s field shapes.
          let sopDemand := mkAlt ((branchShapes.map (peelArrows e2)).mapIdx
            (λ i p => TermShape.Constr (some i) p.1))
          -- refine a bare-`Var` scrutinee toward the reconstructed SOP type
          let e3 := match scrut with
            | .Var v => let (r, ev) := meet e2 (e2.getVar v) sopDemand; ev.setVar v r
            | _      => e2
          -- result: apply branches to known fields, else the robust branch-result join
          match resolved with
          | .Constr none fields =>
              let (results, e4) := applyEachBranch e3 branchShapes fields
              joinAll e4 results
          | _ =>
              joinAll e3 (branchShapes.map caseBranchResult)

/-- Apply a branch shape to `Constr` fields carried as `(fieldTerm, fieldShape)` so field
    variables can be refined. -/
partial def applyToFields (e : Env) (fn : TermShape) : List (Term × TermShape) → TermShape × Env
  | []        => (e.resolve fn, e)
  | (fieldTerm, argShape) :: rest =>
      match e.resolve fn with
      | .Function input output =>
          let (refined, e1) := meet e input argShape
          if refined == .Nothing then (.Nothing, e1)
          else
            let e2 := match fieldTerm with | .Var n => e1.setVar n refined | _ => e1
            applyToFields e2 (e2.resolve output) rest
      | .Anything => applyToFields e .Anything rest
      | .TypeVar n =>
          let (out, e1) := e.fresh
          applyToFields (e1.setCell n (.Function argShape out)) out rest
      | _ => (.Nothing, e)

/-- Apply a branch shape to already-computed field shapes. -/
partial def applyShapes (e : Env) (fn : TermShape) : List TermShape → TermShape × Env
  | []        => (e.resolve fn, e)
  | argShape :: rest =>
      match e.resolve fn with
      | .Function input output =>
          let (refined, e1) := meet e input argShape
          if refined == .Nothing then (.Nothing, e1)
          else applyShapes e1 (e1.resolve output) rest
      | .Anything => applyShapes e .Anything rest
      | .TypeVar n =>
          let (out, e1) := e.fresh
          applyShapes (e1.setCell n (.Function argShape out)) out rest
      | _ => (.Nothing, e)

/-- Apply *every* branch to the fields (unknown-tag `Case`); returns one result per branch. -/
partial def applyEachBranch (e : Env) (branches : List TermShape) (fields : List TermShape)
    : List TermShape × Env :=
  match branches with
  | []      => ([], e)
  | b :: bs =>
      let (r, e1) := applyShapes e b fields
      let (rs, e2) := applyEachBranch e1 bs fields
      (r :: rs, e2)

partial def inferList (e : Env) : List Term → List TermShape × Env
  | []        => ([], e)
  | t :: rest =>
      let (s, e1) := infer e t
      let (ss, e2) := inferList e1 rest
      (s :: ss, e2)

/-- Fuel-bounded fixpoint for a recursive binder: seed `name`'s demand, re-infer the body,
    `meet` the discovered demand back in, and iterate until stable or the fuel runs out.
    Returns the binder's demand, the body's result shape, and the final env. -/
partial def fixLam (base : Env) (name : String) (body : Term) (iters : Nat) (seed : TermShape)
    : TermShape × TermShape × Env :=
  let (bShape, e1) := infer { base with vars := base.vars.insert name seed } body
  match iters with
  | 0      => (zonk e1 (e1.getVar name), bShape, e1)
  | k + 1  =>
      let (acc, e2) := meet e1 seed (e1.getVar name)
      let accZ := zonk e2 acc
      if accZ == zonk e2 seed then (accZ, bShape, e2)
      else fixLam { e2 with vars := base.vars } name body k accZ

end

/-! ## Entry point -/

/-- Free variables of a term. -/
partial def freeVars : Term → List String
  | .Var n       => [n]
  | .Lam n b     => (freeVars b).filter (· != n)
  | .Apply f a   => freeVars f ++ freeVars a
  | .Delay t     => freeVars t
  | .Force t     => freeVars t
  | .Constr _ fs => fs.flatMap freeVars
  | .Case s bs   => freeVars s ++ bs.flatMap freeVars
  | _            => []

/-- Every variable name occurring (free or bound). -/
partial def allVars : Term → List String
  | .Var n       => [n]
  | .Lam n b     => n :: allVars b
  | .Apply f a   => allVars f ++ allVars a
  | .Delay t     => allVars t
  | .Force t     => allVars t
  | .Constr _ fs => fs.flatMap allVars
  | .Case s bs   => allVars s ++ bs.flatMap allVars
  | _            => []

/-- A name not appearing in `avoid`. -/
partial def freshName (base : String) (avoid : List String) (k : Nat) : String :=
  let cand := base ++ "#" ++ toString k
  if avoid.contains cand then freshName base avoid (k + 1) else cand

/-- Capture-avoiding substitution `t[x := v]`. `fvV` is the free variables of `v` (passed in so
    it is computed once). When a binder `n ≠ x` would capture a free `n` of `v`, the binder is
    α-renamed to a fresh name first. -/
partial def substTerm (x : String) (v : Term) (fvV : List String) : Term → Term
  | .Var n       => if n == x then v else .Var n
  | .Lam n b     =>
      if n == x then .Lam n b                       -- x re-bound: stop
      else if fvV.contains n then                   -- would capture: α-rename `n`
        let n' := freshName n (x :: fvV ++ allVars b) 0
        .Lam n' (substTerm x v fvV (substTerm n (.Var n') [n'] b))
      else .Lam n (substTerm x v fvV b)
  | .Apply f a   => .Apply (substTerm x v fvV f) (substTerm x v fvV a)
  | .Delay t     => .Delay (substTerm x v fvV t)
  | .Force t     => .Force (substTerm x v fvV t)
  | .Constr i fs => .Constr i (fs.map (substTerm x v fvV))
  | .Case s bs   => .Case (substTerm x v fvV s) (bs.map (substTerm x v fvV))
  | t            => t

/-- β-substitution `body[x := arg]`, capture-avoiding. -/
def substBeta (x : String) (arg body : Term) : Term := substTerm x arg (freeVars arg) body

/-- Bounded weak-head β/force reduction — collapses the compiler's `let`-preamble (which is
    encoded as a chain of β-redexes) so the script's real argument arity is exposed rather than
    over-counted. -/
partial def whnf : Nat → Term → Term
  | 0,        t => t
  | fuel + 1, t =>
    match t with
    | .Apply f a =>
        match whnf fuel f with
        | .Lam x b => whnf fuel (substBeta x a b)
        | f'       => .Apply f' a
    | .Force t =>
        match whnf fuel t with
        | .Delay d => whnf fuel d
        | t'       => .Force t'
    | t => t

/-- Entry point: the success-typing shape of a UPLC term. Runs bounded weak-head reduction
    (`whnf`) to collapse the compiler's β-redex `let`-preamble and expose the real argument arity,
    infers a shape in a fresh `Env`, then `zonk`s it into a display-ready shape (cells resolved,
    growable views materialised). Engine-`partial`; a developer tool only, never used in proofs. -/
def analyzeType (t : Term) : TermShape :=
  let (s, e) := infer Env.empty (whnf 1000000 t)
  zonk e s

end Internal

export Internal
  (
    TermShape
    analyzeType
  )

end PlutusCore.UPLC.Shape
