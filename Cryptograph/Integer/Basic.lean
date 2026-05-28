namespace Cryptograph.Integer

namespace Internal

def UInt32.toUInt8BE (x : UInt32) : ByteArray :=
  let x₀ := x
  let x₁ := x₀ >>> 8
  let x₂ := x₁ >>> 8
  let x₃ := x₂ >>> 8
  ⟨#[ UInt32.toUInt8 x₃, UInt32.toUInt8 x₂, UInt32.toUInt8 x₁, UInt32.toUInt8 x₀ ]⟩

def UInt64.toUInt8BE (x : UInt64) : ByteArray :=
  let x₁ := x >>> 32
  UInt32.toUInt8BE (UInt64.toUInt32 x₁) ++ UInt32.toUInt8BE (UInt64.toUInt32 x)

def UInt128.toUInt8BE (n : Nat) : ByteArray :=
  UInt64.toUInt8BE (n >>> 64).toUInt64 ++ UInt64.toUInt8BE n.toUInt64

/-- Read 4 bytes from a `ByteArray` starting at offset `i` as a big-endian `UInt32`.
    Out-of-bounds reads return `0` for the missing bytes (matching `ByteArray.get!`). -/
def UInt32.ofUInt8BE (b : ByteArray) (i : Nat := 0) : UInt32 :=
  (UInt8.toUInt32 (b.get!  i     )) <<< 24 |||
  (UInt8.toUInt32 (b.get! (i + 1))) <<< 16 |||
  (UInt8.toUInt32 (b.get! (i + 2))) <<<  8 |||
   UInt8.toUInt32 (b.get! (i + 3))

def rotr (n : Fin 32) (x : UInt32) : UInt32 := let n' := UInt32.ofNat n; x >>> n' ||| x <<< (32 - n')
def shr  (n : Fin 32) (x : UInt32) : UInt32 := let n' := UInt32.ofNat n; x >>> n'

end Internal

export Internal
  (
    UInt32.toUInt8BE
    UInt32.ofUInt8BE
    UInt64.toUInt8BE
    UInt128.toUInt8BE
    rotr
    shr
  )

end Cryptograph.Integer
