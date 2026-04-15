namespace Cryptograph.String

namespace Internal

def String.toByteList (x : String) : List UInt8 := x.toUTF8.toList

def byteListToHex {α} {n} (f : α → BitVec n) (x : List α) : String :=
  let rec loop (acc : List Char) : List α → String
    | h :: t => loop ((h |> f |> BitVec.toHex |> String.data |> List.reverse) ++ acc) t
    | []     => ⟨List.reverse acc⟩
  loop [] x

def uint8ListToHex  (x : List UInt8 ) : String := byteListToHex UInt8.toBitVec  x
def uint32ListToHex (x : List UInt32) : String := byteListToHex UInt32.toBitVec x

end Internal

export Internal
  (
    String.toByteList
    uint8ListToHex
    uint32ListToHex
  )

end Cryptograph.String
