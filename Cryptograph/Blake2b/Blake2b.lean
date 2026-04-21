import Cryptograph.String
import Cryptograph.Integer

namespace Cryptograph.Blake2b.Blake2b

/-! ## Blake2b Hash Implementation-/

namespace Internal

-- Blake2b initialization vectors (first 64 bits of fractional parts of sqrt of first 8 primes)
private def iv : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

-- Sigma permutations for message scheduling (12 rounds)
private def sigma : Array (Array Nat) :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]]

/-! ### Helper Functions -/

-- Rotate right 64-bit value
private def rotr64 (x : UInt64) (n : Nat) : UInt64 :=
  let n := n % 64
  (x >>> n.toUInt64) ||| (x <<< (64 - n).toUInt64)

-- Convert 8 bytes (little-endian) to UInt64
private def bytesToUInt64LE (bytes : ByteArray) (offset : Nat) : UInt64 :=
  let b0 := if offset + 0 < bytes.size then bytes[offset + 0]!.toUInt64 else 0
  let b1 := if offset + 1 < bytes.size then bytes[offset + 1]!.toUInt64 else 0
  let b2 := if offset + 2 < bytes.size then bytes[offset + 2]!.toUInt64 else 0
  let b3 := if offset + 3 < bytes.size then bytes[offset + 3]!.toUInt64 else 0
  let b4 := if offset + 4 < bytes.size then bytes[offset + 4]!.toUInt64 else 0
  let b5 := if offset + 5 < bytes.size then bytes[offset + 5]!.toUInt64 else 0
  let b6 := if offset + 6 < bytes.size then bytes[offset + 6]!.toUInt64 else 0
  let b7 := if offset + 7 < bytes.size then bytes[offset + 7]!.toUInt64 else 0
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

-- Convert UInt64 to 8 bytes (little-endian)
private def uint64ToBytes (x : UInt64) : Array UInt8 :=
  #[(x &&& 0xFF).toUInt8,
    ((x >>> 8) &&& 0xFF).toUInt8,
    ((x >>> 16) &&& 0xFF).toUInt8,
    ((x >>> 24) &&& 0xFF).toUInt8,
    ((x >>> 32) &&& 0xFF).toUInt8,
    ((x >>> 40) &&& 0xFF).toUInt8,
    ((x >>> 48) &&& 0xFF).toUInt8,
    ((x >>> 56) &&& 0xFF).toUInt8]

/-! ### Blake2b Core Functions -/

-- G mixing function (quarter round)
private def g (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 :=
  let va := v[a]!
  let vb := v[b]!
  let vc := v[c]!
  let vd := v[d]!

  -- First step
  let va := va + vb + x
  let vd := rotr64 (vd ^^^ va) 32
  let vc := vc + vd
  let vb := rotr64 (vb ^^^ vc) 24

  -- Second step
  let va := va + vb + y
  let vd := rotr64 (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr64 (vb ^^^ vc) 63

  v.set! a va |>.set! b vb |>.set! c vc |>.set! d vd

-- Blake2b compression function
private def compress (h : Array UInt64) (m : Array UInt64) (t : UInt64) (f : Bool) : Array UInt64 :=
  -- Initialize working variables
  let v := Array.replicate 16 0
  let v := (List.range 8).foldl (fun v i => v.set! i h[i]!) v
  let v := (List.range 8).foldl (fun v i => v.set! (i + 8) iv[i]!) v

  -- Mix the counter and flag
  let v := v.set! 12 (v[12]! ^^^ t)
  let v := if f then v.set! 14 (~~~v[14]!) else v

  -- 12 rounds of mixing
  let v := (List.range 12).foldl (fun v round =>
    let s := sigma[round]!
    let v := g v 0 4  8 12 m[s[0]!]! m[s[1]!]!
    let v := g v 1 5  9 13 m[s[2]!]! m[s[3]!]!
    let v := g v 2 6 10 14 m[s[4]!]! m[s[5]!]!
    let v := g v 3 7 11 15 m[s[6]!]! m[s[7]!]!
    let v := g v 0 5 10 15 m[s[8]!]! m[s[9]!]!
    let v := g v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    let v := g v 2 7  8 13 m[s[12]!]! m[s[13]!]!
    let v := g v 3 4  9 14 m[s[14]!]! m[s[15]!]!
    v
  ) v

  -- XOR the two halves
  (List.range 8).foldl (fun h' i =>
    h'.set! i (h'[i]! ^^^ v[i]! ^^^ v[i + 8]!)
  ) h

-- Parse message block into 16 UInt64 values
private def parseBlock (data : ByteArray) (offset : Nat) : Array UInt64 :=
  Array.range 16 |>.map fun i => bytesToUInt64LE data (offset + i * 8)

/-! ### Main Hash Function -/

-- Blake2b hash with configurable output length
def blake2b (input : List UInt8) (outputLen : Nat) : List UInt8 :=
  if outputLen == 0 || outputLen > 64 then []
  else
    let inputBytes := ByteArray.mk input.toArray
    let inputLen := inputBytes.size

    -- Initialize state with IV XOR parameter block
    -- Parameter block: digest_length || key_length || fanout || depth || ...
    let h := iv.map id  -- Copy IV
    let h := h.set! 0 (h[0]! ^^^ 0x01010000 ^^^ outputLen.toUInt64)

    -- Process full blocks
    let blockSize := 128  -- Blake2b block size in bytes
    let numFullBlocks := (inputLen - 1) / blockSize
    let h := (List.range numFullBlocks).foldl (fun h blockIdx =>
      let offset := blockIdx * blockSize
      let m := parseBlock inputBytes offset
      let t := ((blockIdx + 1) * blockSize).toUInt64
      compress h m t false
    ) h

    -- Process final block (may be partial)
    let finalBlockStart := numFullBlocks * blockSize
    let finalBlockLen := inputLen - finalBlockStart
    let finalBlock := ByteArray.emptyWithCapacity 128
    let finalBlock := (List.range finalBlockLen).foldl (fun arr i =>
      arr.push inputBytes[finalBlockStart + i]!
    ) finalBlock
    -- Pad with zeros
    let finalBlock := (List.range (blockSize - finalBlockLen)).foldl (fun arr _ =>
      arr.push 0
    ) finalBlock

    let m := parseBlock finalBlock 0
    let t := inputLen.toUInt64
    let h := compress h m t true  -- Final block flag

    -- Extract output bytes
    let output := ByteArray.emptyWithCapacity outputLen
    let output := (List.range (outputLen / 8)).foldl (fun arr i =>
      uint64ToBytes h[i]! |>.foldl (fun a b => a.push b) arr
    ) output
    -- Handle remaining bytes if output length is not multiple of 8
    let remainingBytes := outputLen % 8
    let output := if remainingBytes > 0 then
      let lastWord := uint64ToBytes h[outputLen / 8]!
      (List.range remainingBytes).foldl (fun arr i =>
        arr.push lastWord[i]!
      ) output
    else
      output

    output.toList

-- Blake2b-256: 256-bit (32-byte) output
def blake2b_256 (input : List UInt8) : List UInt8 :=
  blake2b input 32

-- Blake2b-224: 224-bit (28-byte) output
def blake2b_224 (input : List UInt8) : List UInt8 :=
  blake2b input 28

-- String versions
def blake2b_256_hash (input : String) : String :=
  let inputBytes := input.toUTF8.toList
  let hashBytes := blake2b_256 inputBytes
  Cryptograph.String.uint8ListToHex hashBytes

def blake2b_224_hash (input : String) : String :=
  let inputBytes := input.toUTF8.toList
  let hashBytes := blake2b_224 inputBytes
  Cryptograph.String.uint8ListToHex hashBytes

end Internal

-- Export main functions
export Internal (blake2b blake2b_256 blake2b_224 blake2b_256_hash blake2b_224_hash)

end Cryptograph.Blake2b.Blake2b
