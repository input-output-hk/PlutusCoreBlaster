import Cryptograph.Integer
import Cryptograph.String

namespace Cryptograph.Sha2.Sha512

/-! ## SHA-512 Hash Implementation-/

namespace Internal

open Cryptograph.Integer
open Cryptograph.String

-- SHA-512 round constants
def k : List UInt64 :=
  [ 0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc
  , 0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118
  , 0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2
  , 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694
  , 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
  , 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5
  , 0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4
  , 0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70
  , 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df
  , 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
  , 0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30
  , 0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8
  , 0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8
  , 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3
  , 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
  , 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b
  , 0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178
  , 0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b
  , 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c
  , 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
  ]

-- Initial hash values
def initial : List UInt64 :=
  [ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
  , 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
  ]

-- Rotate right 64-bit value
def rotr64 (n : Nat) (x : UInt64) : UInt64 :=
  (x >>> n.toUInt64) ||| (x <<< (64 - n).toUInt64)

-- Right shift 64-bit value
def shr64 (n : Nat) (x : UInt64) : UInt64 :=
  x >>> n.toUInt64

-- SHA-512 functions (using ASCII names to avoid Unicode issues)
def bigSigma0 (x : UInt64) : UInt64 := rotr64 28 x ^^^ rotr64 34 x ^^^ rotr64 39 x
def bigSigma1 (x : UInt64) : UInt64 := rotr64 14 x ^^^ rotr64 18 x ^^^ rotr64 41 x
def sigma0 (x : UInt64) : UInt64 := rotr64 1 x ^^^ rotr64 8 x ^^^ shr64 7 x
def sigma1 (x : UInt64) : UInt64 := rotr64 19 x ^^^ rotr64 61 x ^^^ shr64 6 x

def Ch (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (~~~x &&& z)
def Maj (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

-- Convert 8 bytes (big-endian) to UInt64
def bytesToUInt64BE (bytes : List UInt8) (offset : Nat) : UInt64 :=
  let get := fun i => if offset + i < bytes.length then bytes[offset + i]!.toUInt64 else 0
  (get 0 <<< 56) ||| (get 1 <<< 48) ||| (get 2 <<< 40) ||| (get 3 <<< 32) |||
  (get 4 <<< 24) ||| (get 5 <<< 16) ||| (get 6 <<< 8) ||| get 7

-- Pad message
def padMessage (x : List UInt8) : List UInt8 :=
  let l      := List.length x
  let padn   := (240 - ((l + 1) % 128)) % 128
  let zeroes := List.replicate padn 0x00
  if l ≥ 2 ^ 125
    then panic! "Message too long!"
    else x ++ (0x80 :: zeroes) ++ UInt128.toUInt8BE (l * 8)

-- Process one 1024-bit chunk
def processChunk (h : List UInt64) (chunk : List UInt8) : List UInt64 :=
  -- Parse chunk into 16 UInt64 words
  let w0 := List.range 16 |>.map (fun i => bytesToUInt64BE chunk (i * 8))

  -- Extend to 80 words
  let w := (List.range 64).foldl (fun w i =>
    let w16 := w[i]!
    let w15 := w[i + 1]!
    let w7 := w[i + 9]!
    let w2 := w[i + 14]!
    w ++ [sigma1 w2 + w7 + sigma0 w15 + w16]
  ) w0

  -- Initialize working variables
  let a := h[0]!
  let b := h[1]!
  let c := h[2]!
  let d := h[3]!
  let e := h[4]!
  let f := h[5]!
  let g := h[6]!
  let h₀ := h[7]!

  -- 80 rounds
  let (a, b, c, d, e, f, g, h₀) := (List.range 80).zip (w.zip k) |>.foldl (fun (a, b, c, d, e, f, g, h) (_, (wi, ki)) =>
    let T1 := h + bigSigma1 e + Ch e f g + ki + wi
    let T2 := bigSigma0 a + Maj a b c
    (T1 + T2, a, b, c, d + T1, e, f, g)
  ) (a, b, c, d, e, f, g, h₀)

  -- Add to current hash
  [h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
   h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + h₀]

-- Process all chunks
def processChunks (h : List UInt64) (x : List UInt8) : List UInt64 :=
  if x.length < 128 then h
  else
    let chunk := x.take 128
    let h' := processChunk h chunk
    processChunks h' (x.drop 128)
termination_by x.length
decreasing_by simp; omega

-- Main hash function
def hashMessage (x : List UInt8) : List UInt64 :=
  processChunks initial (padMessage x)

-- Hash and return hex string
def hash (x : String) : String :=
  let hashVals := hashMessage x.toByteList
  let bytes := hashVals.flatMap UInt64.toUInt8BE
  uint8ListToHex bytes

end Internal

export Internal (hashMessage hash)

end Cryptograph.Sha2.Sha512
