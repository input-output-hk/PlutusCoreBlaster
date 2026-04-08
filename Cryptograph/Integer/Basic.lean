namespace Cryptograph.Integer

namespace Internal

def UInt32.toUInt8BE (x : UInt32) : List UInt8 :=
  let x₀ := x
  let x₁ := x₀ >>> 8
  let x₂ := x₁ >>> 8
  let x₃ := x₂ >>> 8
  [ UInt32.toUInt8 x₃, UInt32.toUInt8 x₂, UInt32.toUInt8 x₁, UInt32.toUInt8 x₀ ]

def UInt64.toUInt8BE (x : UInt64) : List UInt8 :=
  let x₁ := x >>> 32
  UInt32.toUInt8BE (UInt64.toUInt32 x₁) ++ UInt32.toUInt8BE (UInt64.toUInt32 x)

def UInt32.ofUInt8BE (x : Vector UInt8 4) : UInt32 :=
  (UInt8.toUInt32 x[0]) <<< 24 ||| (UInt8.toUInt32 x[1]) <<< 16 ||| (UInt8.toUInt32 x[2]) <<< 8 ||| UInt8.toUInt32 x[3]

def rotr (n : Fin 32) (x : UInt32) : UInt32 := let n' := UInt32.ofNat n; x >>> n' ||| x <<< (32 - n')
def shr  (n : Fin 32) (x : UInt32) : UInt32 := let n' := UInt32.ofNat n; x >>> n'

end Internal

export Internal
  (
    UInt32.toUInt8BE
    UInt32.ofUInt8BE
    UInt64.toUInt8BE
    rotr
    shr
  )

end Cryptograph.Integer
