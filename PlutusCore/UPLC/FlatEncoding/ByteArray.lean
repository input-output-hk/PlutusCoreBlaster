import PlutusCore.UPLC.FlatEncoding.Basic

/-! Flat decoding from raw bytes. Positions are bit offsets, so aligned byte payloads
can be copied directly without materializing eight list nodes per input byte.
The list decoder remains available as an independent differential reference. -/
namespace PlutusCore.UPLC.FlatEncoding

open PlutusCore.UPLC.Term
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Cbor (decodeData)
open PlutusCore.String (decodeUtf8)

namespace ByteDecoder

/-- Read up to eight bits, most significant bit first. The bounds check precedes
    every array access, including the unaligned two-byte case. -/
@[inline] def fixed (bytes : ByteArray) (width pos : Nat) : Option (Nat × Nat) :=
  if width == 0 then some (pos, 0)
  else if width ≤ 8 && pos + width ≤ bytes.size * 8 then
    let index := pos / 8
    let offset := pos % 8
    let first := UInt16.ofNat bytes[index]!.toNat
    let value := if offset + width ≤ 8 then
        first >>> UInt16.ofNat (8 - offset - width)
      else
        let second := UInt16.ofNat bytes[index + 1]!.toNat
        ((first <<< 8) ||| second) >>> UInt16.ofNat (16 - offset - width)
    some (pos + width, (value &&& ((1 <<< UInt16.ofNat width) - 1)).toNat)
  else none

def naturalLoop (bytes : ByteArray) : Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _ => none
  | remaining + 1, pos, acc, factor => do
      let (pos, byte) ← fixed bytes 8 pos
      let acc := acc + (byte % 128) * factor
      if byte < 128 then some (pos, acc)
      else naturalLoop bytes remaining pos acc (factor * 128)

def natural (bytes : ByteArray) (pos : Nat) : Option (Nat × Nat) :=
  naturalLoop bytes ((bytes.size * 8 - pos) / 8) pos 0 1

def integer (bytes : ByteArray) (pos : Nat) : Option (Nat × Int) := do
  let (pos, n) ← natural bytes pos
  return (pos, if n % 2 == 0 then Int.ofNat (n / 2) else -(Int.ofNat n + 1) / 2)

/-- Match the reference's permissive padding: one to eight bits ending in one.
    Byte alignment is not imposed here, so accepted unaligned inputs stay accepted. -/
def padding (bytes : ByteArray) : Nat → Nat → Option Nat
  | 0, _ => none
  | remaining + 1, pos => do
      let (pos, bit) ← fixed bytes 1 pos
      if bit == 1 then some pos else padding bytes remaining pos

def unalignedBytes (bytes : ByteArray) : Nat → Nat → ByteArray → Option (Nat × ByteArray)
  | 0, pos, acc => some (pos, acc)
  | n + 1, pos, acc => do
      let (pos, byte) ← fixed bytes 8 pos
      unalignedBytes bytes n pos (acc.push byte.toUInt8)

def rawBytes (bytes : ByteArray) (pos length : Nat) : Option (Nat × ByteArray) :=
  if pos + length * 8 ≤ bytes.size * 8 then
    if pos % 8 == 0 then
      some (pos + length * 8, bytes.extract (pos / 8) (pos / 8 + length))
    else unalignedBytes bytes length pos ByteArray.empty
  else none

partial def chunks (bytes : ByteArray) (pos : Nat) (acc : ByteArray) : Option (Nat × ByteArray) := do
  let (pos, length) ← fixed bytes 8 pos
  if length == 0 then return (pos, acc)
  let (pos, chunk) ← rawBytes bytes pos length
  chunks bytes pos (acc ++ chunk)

def bytestring (bytes : ByteArray) (pos : Nat) : Option (Nat × String) := do
  let pos ← padding bytes 8 pos
  let (pos, payload) ← chunks bytes pos ByteArray.empty
  return (pos, String.mk (payload.data.toList.map Char.ofUInt8))

def unicode (bytes : ByteArray) (pos : Nat) : Option (Nat × String) := do
  let (pos, payload) ← bytestring bytes pos
  let text ← Except.toOption (decodeUtf8 payload)
  return (pos, text)

def boolean (bytes : ByteArray) (pos : Nat) : Option (Nat × Bool) := do
  let (pos, bit) ← fixed bytes 1 pos
  return (pos, bit == 1)

partial def list {α : Type} (bytes : ByteArray) (read : Nat → Option (Nat × α))
    (pos : Nat) : Option (Nat × List α) := do
  let (pos, more) ← fixed bytes 1 pos
  if more == 0 then return (pos, [])
  let (pos, value) ← read pos
  let (pos, values) ← list bytes read pos
  return (pos, value :: values)

partial def constantValue (bytes : ByteArray) (s : Nat) : BuiltinType → Option (Nat × Const)
  | .AtomicType .TypeInteger        => Prod.map id .Integer                      <$> integer bytes s
  | .AtomicType .TypeByteString     => Prod.map id (.ByteString ∘ ByteString.mk) <$> bytestring bytes s
  | .AtomicType .TypeString         => Prod.map id .String                       <$> unicode bytes s
  | .AtomicType .TypeUnit           => .some (s, .Unit)
  | .AtomicType .TypeBool           => Prod.map id .Bool                         <$> boolean bytes s
  | .AtomicType .TypeData           => do
      let (s', t) ← bytestring bytes s
      let (_ , d) ← decodeData t
      .some (s', .Data d)
  | .TypeOperator (.TypeList t)     =>
       match t with
       | .AtomicType .TypeData =>
             let decodeConstData (xs : Nat) : Option (Nat × Data) :=
               match constantValue bytes xs t with
               | some (xs', Const.Data d) => some (xs', d)
               | _ => none -- don't produce anything on type mismatched
             Prod.map id Const.ConstDataList <$> list bytes decodeConstData s
       | .TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)) =>
             let decodeConstPairData (xs : Nat) : Option (Nat × (Data × Data)) :=
               match constantValue bytes xs t with
               | some (xs', Const.PairData p) => some (xs', p)
               | _ => none -- don't produce anything on type mismatched
             Prod.map id .ConstPairDataList <$> list bytes decodeConstPairData s
       | _ => Prod.map id Const.ConstList <$> list bytes (fun s => constantValue bytes s t) s -- heterogenous list
  | .TypeOperator (.TypePair t₁ t₂) => do
      let (s₁, c₁) ← constantValue bytes s  t₁
      let (s₂, c₂) ← constantValue bytes s₁ t₂
      match t₁, t₂ with
      | .AtomicType .TypeData, .AtomicType .TypeData =>
          match c₁, c₂ with
          | Const.Data d₁, Const.Data d₂ => some (s₂, Const.PairData (d₁, d₂))
          | _, _ => none
      | _, _ => some (s₂, Const.Pair (c₁, c₂))
  | .AtomicType .TypeBls12_381_G1_element -- BLS values are not serializable
  | .AtomicType .TypeBls12_381_G2_element
  | .AtomicType .TypeBls12_381_MlResult   => none


def constant (bytes : ByteArray) (pos : Nat) : Option (Nat × Const) := do
  let (pos, tags) ← list bytes (fixed bytes 4) pos
  let (rest, type) ← Internal.decodeConstType tags
  if !rest.isEmpty then none else constantValue bytes pos type

private def builtinArray : Array (Option BuiltinFun) :=
  ((List.range 128).map (fun n => List.lookup n Internal.builtinTable)).toArray

def builtin (bytes : ByteArray) (pos : Nat) : Option (Nat × BuiltinFun) := do
  let (pos, index) ← fixed bytes 7 pos
  let value ← builtinArray[index]?.join
  return (pos, value)

partial def term (bytes : ByteArray) (version : Version) (pos : Nat) : Option (Nat × Term) := do
  let (pos, tag) ← fixed bytes 4 pos
  match tag with
  | 0 =>
      let (pos, index) ← natural bytes pos
      if index == 0 then none else some (pos, .Var (index - 1))
  | 1 => Prod.map id Term.Delay <$> term bytes version pos
  | 2 => Prod.map id Term.Lam <$> term bytes version pos
  | 3 =>
      let (pos, fn) ← term bytes version pos
      let (pos, arg) ← term bytes version pos
      return (pos, .Apply fn arg)
  | 4 => Prod.map id Term.Term.Const <$> constant bytes pos
  | 5 => Prod.map id Term.Force <$> term bytes version pos
  | 6 => some (pos, .Error)
  | 7 => Prod.map id Term.Builtin <$> builtin bytes pos
  | 8 =>
      if version < .Version 1 1 0 then none else do
        let (pos, index) ← natural bytes pos
        if index ≥ 2 ^ 64 then none else do
          let (pos, args) ← list bytes (term bytes version) pos
          return (pos, .Constr index args)
  | 9 =>
      if version < .Version 1 1 0 then none else do
        let (pos, scrutinee) ← term bytes version pos
        let (pos, branches) ← list bytes (term bytes version) pos
        return (pos, .Case scrutinee branches)
  | _ => none

def program (bytes : ByteArray) : Option Program := do
  let (pos, major) ← natural bytes 0
  let (pos, minor) ← natural bytes pos
  let (pos, patch) ← natural bytes pos
  let version := Version.Version major minor patch
  let (pos, body) ← term bytes version pos
  let pos ← padding bytes 8 pos
  if pos == bytes.size * 8 then some (.Program version body) else none

end ByteDecoder

/-- Decode raw Flat bytes without expanding the input into a list of bits. -/
def decodeProgramFromBytes := ByteDecoder.program

end PlutusCore.UPLC.FlatEncoding
