import PlutusCore.Crypto.Hash
import PlutusCore.Crypto.Ed25519
import PlutusCore.Crypto.Native.ByteString

/-! Native conformance test driver, not a theorem generator. TSV inputs and expected values
come from hashlib, fixed Keccak vectors and pinned Wycheproof Ed25519 vectors. -/

namespace Benchmark.Cek.CryptoProbe

open PlutusCore.ByteString (ByteString)
open PlutusCore.Crypto.Hash
open PlutusCore.Crypto.Ed25519

private def nibble (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else .error "invalid lowercase hex"

private def unhex : List Char → Except String (List Char)
  | [] => .ok []
  | a :: b :: rest => do
    let byte := 16 * (← nibble a) + (← nibble b)
    return Char.ofNat byte :: (← unhex rest)
  | _ => .error "odd hex length"

private def input (hex : String) : IO ByteString := do
  if hex == "unicode" then return ⟨"éĀ🙂"⟩
  return ⟨String.mk (← IO.ofExcept (unhex hex.data))⟩

private def hashes : String → Option ((ByteString → ByteString) × (ByteString → ByteString))
  | "sha2_256" => some (sha2_256, sha2_256Reference)
  | "sha3_256" => some (sha3_256, sha3_256Reference)
  | "blake2b_256" => some (blake2b_256, blake2b_256Reference)
  | "blake2b_224" => some (blake2b_224, blake2b_224Reference)
  | "keccak_256" => some (keccak_256, keccak_256Reference)
  | "ripemd_160" => some (ripemd_160, ripemd_160Reference)
  | _ => none

private def hex (bs : ByteString) : String :=
  Cryptograph.String.uint8ListToHex (bs.data.data.map Char.toUInt8)

def checkLine (line : String) : IO Unit := do
  let [kind, label, a, b, c, expected] := line.splitOn "\t"
    | throw (IO.userError "expected six TSV fields")
  if let some (native, reference) := hashes kind then
    let x ← input a
    let actual := native x
    let ref := reference x
    unless actual == ref do throw (IO.userError s!"{label}: hash native/reference mismatch")
    unless expected == "either" || hex actual == expected do
      throw (IO.userError s!"{label}: wrong digest {hex actual}; expected {expected}")
  else if kind == "ed25519" then
    let pk ← input a
    let msg ← input b
    let sig ← input c
    let actual := verifyEd25519Signature pk msg sig
    let ref := verifyEd25519SignatureReference pk msg sig
    let same := match actual, ref with
      | .ok a, .ok b => a == b
      | .error a, .error b => a == b
      | _, _ => false
    unless same do
      throw (IO.userError s!"{label}: Ed25519 native/reference mismatch: {repr actual} vs {repr ref}")
    let value := match actual with
      | .ok true => "true"
      | .ok false => "false"
      | .error _ => "error"
    unless expected == "either" || value == expected do
      throw (IO.userError s!"{label}: Ed25519 {value}; expected {expected}")
  else throw (IO.userError s!"unknown primitive {kind}")

end Benchmark.Cek.CryptoProbe

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: test_crypto_ffi VECTORS.tsv"
    return (2 : UInt32)
  try
    let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· != "")
    for line in lines do Benchmark.Cek.CryptoProbe.checkLine line
    IO.println s!"Native/reference crypto conformity: {lines.length} cases passed"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"CRYPTO_FAIL: {error}"
    return (1 : UInt32)
