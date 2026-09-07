namespace Cryptograph.String

namespace Internal

/-- UTF-8 encoded bytes of a string. -/
def String.toByteArray (x : String) : ByteArray := x.toUTF8

private def hexNibble : UInt8 → Char
  |  0 => '0'
  |  1 => '1'
  |  2 => '2'
  |  3 => '3'
  |  4 => '4'
  |  5 => '5'
  |  6 => '6'
  |  7 => '7'
  |  8 => '8'
  |  9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | 15 => 'f'
  | _  => '?'

/-- Hex-string encoding of a `ByteArray` (lowercase, no separators). -/
def byteArrayToHex (b : ByteArray) : String :=
  let chars := b.foldl (init := #[]) (fun acc byte =>
    let hi := byte >>> 4
    let lo := byte &&& 0x0F
    acc.push (hexNibble hi) |>.push (hexNibble lo))
  ⟨chars.toList⟩

private def byteListToHex {α} {n} (f : α → BitVec n) (x : List α) : String :=
  let rec loop (acc : List Char) : List α → String
    | h :: t => loop ((h |> f |> BitVec.toHex |> String.data |> List.reverse) ++ acc) t
    | []     => ⟨List.reverse acc⟩
  loop [] x

/-- Hex-string encoding of a list of 32-bit words. -/
def uint32ListToHex (x : List UInt32) : String := byteListToHex UInt32.toBitVec x

end Internal

export Internal
  (
    String.toByteArray
    byteArrayToHex
    uint32ListToHex
  )

end Cryptograph.String
