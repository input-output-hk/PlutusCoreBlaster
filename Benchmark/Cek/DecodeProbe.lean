import PlutusCore.UPLC.FlatEncoding

/-! Compare complete parsed ASTs, without evaluating untrusted/fuzzed programs. -/
namespace Benchmark.Cek.DecodeProbe

open PlutusCore.UPLC.FlatEncoding

private def nibble (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else .error "invalid lowercase hex"

private def unhex : List Char → ByteArray → Except String ByteArray
  | [], acc => .ok acc
  | a :: b :: rest, acc => do
      let byte := 16 * (← nibble a) + (← nibble b)
      unhex rest (acc.push byte.toUInt8)
  | _, _ => .error "odd hex length"

def checkLine (line : String) : IO Unit := do
  let [label, encoded] := line.splitOn "\t"
    | throw (IO.userError "expected label and hex")
  let bytes ← IO.ofExcept (unhex encoded.data ByteArray.empty)
  let input := String.mk (bytes.data.toList.map Char.ofUInt8)
  let reference := decodeProgramFromByteString input
  let actual := decodeProgramFromBytes bytes
  unless actual == reference do
    throw (IO.userError s!"{label}: byte decoder differs from the complete reference AST")
  IO.println s!"{label}\t{if actual.isSome then "accepted" else "rejected"}"

end Benchmark.Cek.DecodeProbe

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: test_flat_decode VECTORS.tsv"
    return (2 : UInt32)
  try
    for line in (← IO.FS.readFile path).splitOn "\n" do
      unless line.isEmpty do Benchmark.Cek.DecodeProbe.checkLine line
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)
