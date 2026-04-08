import Cryptograph.String
import Cryptograph.Integer

namespace Cryptograph.Ripemd.Ripemd160

/-! ## RIPEMD-160 Hash Implementation-/

namespace Internal

open Cryptograph.Integer

-- Initial hash values
private def h0 : UInt32 := 0x67452301
private def h1 : UInt32 := 0xEFCDAB89
private def h2 : UInt32 := 0x98BADCFE
private def h3 : UInt32 := 0x10325476
private def h4 : UInt32 := 0xC3D2E1F0

-- Left path message selection order (for each round)
private def zl : Array (Array Nat) :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #[7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8],
    #[3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12],
    #[1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2],
    #[4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]]

-- Right path message selection order (for each round)
private def zr : Array (Array Nat) :=
  #[#[5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12],
    #[6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2],
    #[15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13],
    #[8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14],
    #[12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]]

-- Left path rotation amounts
private def sl : Array (Array Nat) :=
  #[#[11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8],
    #[7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12],
    #[11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5],
    #[11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12],
    #[9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]]

-- Right path rotation amounts
private def sr : Array (Array Nat) :=
  #[#[8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6],
    #[9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11],
    #[9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5],
    #[15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8],
    #[8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]]

/-! ### Helper Functions -/

-- Nonlinear functions for left path
private def f (j : Nat) (x y z : UInt32) : UInt32 :=
  match j / 16 with
  | 0 => x ^^^ y ^^^ z                           -- Round 1
  | 1 => (x &&& y) ||| ((~~~x) &&& z)            -- Round 2
  | 2 => (x ||| (~~~y)) ^^^ z                    -- Round 3
  | 3 => (x &&& z) ||| (y &&& (~~~z))            -- Round 4
  | _ => x ^^^ (y ||| (~~~z))                    -- Round 5

-- Nonlinear functions for right path
private def g (j : Nat) (x y z : UInt32) : UInt32 :=
  match j / 16 with
  | 0 => x ^^^ (y ||| (~~~z))                    -- Round 1
  | 1 => (x &&& z) ||| (y &&& (~~~z))            -- Round 2
  | 2 => (x ||| (~~~y)) ^^^ z                    -- Round 3
  | 3 => (x &&& y) ||| ((~~~x) &&& z)            -- Round 4
  | _ => x ^^^ y ^^^ z                           -- Round 5

-- Left path constants
private def kl (j : Nat) : UInt32 :=
  match j / 16 with
  | 0 => 0x00000000
  | 1 => 0x5A827999
  | 2 => 0x6ED9EBA1
  | 3 => 0x8F1BBCDC
  | _ => 0xA953FD4E

-- Right path constants
private def kr (j : Nat) : UInt32 :=
  match j / 16 with
  | 0 => 0x50A28BE6
  | 1 => 0x5C4DD124
  | 2 => 0x6D703EF3
  | 3 => 0x7A6D76E9
  | _ => 0x00000000

-- Convert 4 bytes (little-endian) to UInt32
private def bytesToUInt32LE (bytes : ByteArray) (offset : Nat) : UInt32 :=
  let b0 := if offset + 0 < bytes.size then bytes[offset + 0]!.toUInt32 else 0
  let b1 := if offset + 1 < bytes.size then bytes[offset + 1]!.toUInt32 else 0
  let b2 := if offset + 2 < bytes.size then bytes[offset + 2]!.toUInt32 else 0
  let b3 := if offset + 3 < bytes.size then bytes[offset + 3]!.toUInt32 else 0
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

-- Convert UInt32 to 4 bytes (little-endian)
private def uint32ToBytes (x : UInt32) : Array UInt8 :=
  #[(x &&& 0xFF).toUInt8,
    ((x >>> 8) &&& 0xFF).toUInt8,
    ((x >>> 16) &&& 0xFF).toUInt8,
    ((x >>> 24) &&& 0xFF).toUInt8]

/-! ### RIPEMD-160 Compression Function -/

-- Process a single 512-bit block
private def compress (h : Array UInt32) (block : Array UInt32) : Array UInt32 :=
  -- Initialize working variables for both paths
  let al := h[0]!
  let bl := h[1]!
  let cl := h[2]!
  let dl := h[3]!
  let el := h[4]!

  let ar := al
  let br := bl
  let cr := cl
  let dr := dl
  let er := el

  -- Process 80 steps (5 rounds × 16 steps each)
  let rec processSteps (j : Nat) (al bl cl dl el ar br cr dr er : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 :=
    if j >= 80 then (al, bl, cl, dl, el, ar, br, cr, dr, er)
    else
      let round := j / 16
      let step := j % 16

      -- Left path (uses left rotation)
      let t := al + f j bl cl dl + block[zl[round]![step]!]! + kl j
      let s := sl[round]![step]!
      let t := (t <<< s.toUInt32) ||| (t >>> (32 - s).toUInt32)  -- Left rotation
      let t := t + el
      let al := el
      let el := dl
      let dl := (cl <<< 10) ||| (cl >>> 22)  -- Left rotation by 10
      let cl := bl
      let bl := t

      -- Right path (uses left rotation)
      let t := ar + g j br cr dr + block[zr[round]![step]!]! + kr j
      let s := sr[round]![step]!
      let t := (t <<< s.toUInt32) ||| (t >>> (32 - s).toUInt32)  -- Left rotation
      let t := t + er
      let ar := er
      let er := dr
      let dr := (cr <<< 10) ||| (cr >>> 22)  -- Left rotation by 10
      let cr := br
      let br := t

      processSteps (j + 1) al bl cl dl el ar br cr dr er

  let (al, bl, cl, dl, el, ar, br, cr, dr, er) :=
    processSteps 0 al bl cl dl el ar br cr dr er

  -- Combine results according to RIPEMD-160 spec
  #[h[1]! + cl + dr,
    h[2]! + dl + er,
    h[3]! + el + ar,
    h[4]! + al + br,
    h[0]! + bl + cr]

-- Pad message according to MD4 padding (same as MD5/SHA-1)
private def padMessage (msg : ByteArray) : ByteArray :=
  let msgLen := msg.size
  let bitLen := msgLen * 8

  -- Append 0x80 byte
  let padded := msg.push 0x80

  -- Pad with zeros until length ≡ 56 (mod 64)
  let padLen := (56 - (msgLen + 1) % 64) % 64
  let padded := (List.range padLen).foldl (fun arr _ => arr.push 0) padded

  -- Append length as 64-bit little-endian integer
  let padded := (List.range 8).foldl (fun arr i =>
    arr.push ((bitLen >>> (i * 8)) % 256).toUInt8
  ) padded

  padded

-- Parse 512-bit block into 16 UInt32 words
private def parseBlock (data : ByteArray) (offset : Nat) : Array UInt32 :=
  Array.range 16 |>.map fun i => bytesToUInt32LE data (offset + i * 4)

/-! ### Main Hash Function -/

-- RIPEMD-160 hash function
def ripemd160 (input : List UInt8) : List UInt8 :=
  let inputBytes := ByteArray.mk input.toArray
  let padded := padMessage inputBytes

  -- Initialize hash state
  let h := #[h0, h1, h2, h3, h4]

  -- Process all 512-bit blocks
  let numBlocks := padded.size / 64
  let h := (List.range numBlocks).foldl (fun h blockIdx =>
    let offset := blockIdx * 64
    let block := parseBlock padded offset
    compress h block
  ) h

  -- Convert hash state to bytes (little-endian)
  let output := h.foldl (fun arr word =>
    uint32ToBytes word |>.foldl (fun a b => a.push b) arr
  ) ByteArray.empty

  output.toList

-- String version
def ripemd160_hash (input : String) : String :=
  let inputBytes := input.toUTF8.toList
  let hashBytes := ripemd160 inputBytes
  Cryptograph.String.uint8ListToHex hashBytes

end Internal

-- Export main functions
export Internal (ripemd160 ripemd160_hash)

end Cryptograph.Ripemd.Ripemd160
