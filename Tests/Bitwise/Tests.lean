import PlutusCore.Bitwise.Basic

open PlutusCore.Integer
open PlutusCore.Bitwise.BitwiseInternal

namespace PlutusCore.Bitwise

/-! ## Theorems on Logical and Bitwise builtin functions. -/

def Except.isError (e : Except ε α) : Bool := not (Except.isOk e)

example : integerToByteString false 5 0x123456 = .ok "\x56\x34\x12\x00\x00" := rfl
example : integerToByteString false 4 0x123456 = .ok "\x56\x34\x12\x00"     := rfl
example : integerToByteString false 3 0x123456 = .ok "\x56\x34\x12"         := rfl
example : integerToByteString false 2 0x123456 |> Except.isError            := rfl
example : integerToByteString false 0 0x00     = .ok ""                     := by simp [integerLog2] ; rfl

example : integerToByteString true  5 0x123456 = .ok "\x00\x00\x12\x34\x56" := rfl
example : integerToByteString true  4 0x123456 = .ok     "\x00\x12\x34\x56" := rfl
example : integerToByteString true  3 0x123456 = .ok         "\x12\x34\x56" := rfl
example : integerToByteString true  2 0x123456 |> Except.isError            := rfl
example : integerToByteString true  0 0x00     = .ok ""                     := by simp [integerLog2]; rfl


example : repr256_le (String.toList "\x56\x34\x12\x00\x00") = 0x123456 := rfl
example : repr256_le (String.toList "\x56\x34\x12\x00"    ) = 0x123456 := rfl
example : repr256_le (String.toList "\x56\x34\x12"        ) = 0x123456 := rfl


example : repr256_be (String.toList "\x00\x00\x12\x34\x56") = 0x123456 := rfl
example : repr256_be (String.toList     "\x00\x12\x34\x56") = 0x123456 := rfl
example : repr256_be (String.toList         "\x12\x34\x56") = 0x123456 := rfl


example : andByteString true  "\xA5\xFF" "\x5A" = "\x00\xFF" := rfl
example : andByteString false "\xA5\xFF" "\x5A" = "\x00"     := rfl

-- TODO: formalizations for andByteString

example :  orByteString true  "\xA5\xFF" "\x5A" = "\xFF\xFF" := rfl
example :  orByteString false "\xA5\xFF" "\x5A" = "\xFF"     := rfl

-- TODO: formalizations for orByteString

example : xorByteString true  "\xAF\xFF" "\x5A" = "\xF5\xFF" := rfl
example : xorByteString false "\xAF\xFF" "\x5A" = "\xF5"     := rfl

-- TODO: formalizations for xorByteString

example : complementByteString "\xA5\x5F" = "\x5A\xA0" := by native_decide

-- TODO: formalizations for complementByteString

example : shiftByteString "\xA5\x5F"   1  = "\x4A\xBE" := rfl
example : shiftByteString "\xCA\xFE"   4  = "\xAF\xE0" := rfl
example : shiftByteString "\xCA\xFE" (-4) = "\x0C\xAF" := rfl

-- TODO: formalizations for shiftByteString

example : rotateByteString "\xA5\x5F"   1  = "\x4A\xBF" := rfl
example : rotateByteString "\xCA\xFE"   4  = "\xAF\xEC" := rfl
example : rotateByteString "\xCA\xFE" (-4) = "\xEC\xAF" := rfl

-- TODO: formalizations for rotateByteString

example : countSetBits "\xF0"     = 4 := rfl
example : countSetBits "\xA5"     = 4 := rfl
example : countSetBits "\xFF\x00" = 8 := rfl

-- TODO: formalizations for countSetBits

example : findFirstSetBit "\xF0"     = 4 := rfl
example : findFirstSetBit "\xFF\x00" = 8 := rfl
example : findFirstSetBit "\xFF\x01" = 0 := rfl

-- TODO: formalizations for firstSetBit

example : readBit "\xA5"      8 = .error "readBit: index out of bounds" := rfl
example : readBit "\xA5"      3 = .ok false                             := rfl
example : readBit "\xA5"      7 = .ok true                              := rfl
example : readBit "\xA5\x00"  3 = .ok false                             := rfl
example : readBit "\xA5\x00" 14 = .ok false                             := rfl
example : readBit "\xA5\x00" 15 = .ok true                              := rfl

-- TODO: formalizations for readBit

example : writeBit "\x00\x00"  0 true  = .ok "\x00\x01" := rfl
example : writeBit "\x00\x01"  0 true  = .ok "\x00\x01" := rfl
example : writeBit "\x00\x01" 15 true  = .ok "\x80\x01" := rfl
example : writeBit "\x80\x01"  0 false = .ok "\x80\x00" := rfl

-- TODO: formalizations for writeBit

example : writeBits "\x00\x00" [15, 13, 8, 10]    true  = .ok "\xA5\x00" := rfl
example : writeBits "\x00\x00" [15, 13, 8, 10]    false = .ok "\x00\x00" := rfl
example : writeBits "\xFF\xFF" [0, 13, 12, 8, 10] false = .ok "\xCA\xFE" := rfl

-- TODO: formalizations for writeBits

example : replicateByte    4 101 = .ok "eeee" := rfl
example : replicateByte (-4) 101 = .error "replicateByte: negative length requested" := rfl

end PlutusCore.Bitwise
