import Cryptograph.Integer
import Cryptograph.String

namespace Cryptograph.Sha2.Sha256

namespace Internal

open Cryptograph.Integer
open Cryptograph.String

def k : Vector UInt32 64 :=
  #v[ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
    , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
    , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
    , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
    , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
    , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
    , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
    , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ]

def List.pairs {α} (x : List α) : List (α × α) :=
  let rec loop (acc : List (α × α)) : List α → List (α × α)
    | h₁ :: h₂ :: t => loop ((h₁, h₂) :: acc) t
    | _             => List.reverse acc
  loop [] x

def UInt32.listOfUInt8 (x : List UInt8) : List UInt32 :=
  List.map (λ ((b₀, b₁), b₂, b₃) => UInt32.ofUInt8BE #v[b₀, b₁, b₂, b₃]) (List.pairs (List.pairs x))

def padMessage (x : List UInt8) : List UInt8 :=
  let l      := List.length x
  let padn   := (120 - ((l + 1) % 64)) % 64
  let zeroes := List.replicate padn 0x00
  if l ≥ 2 ^ 64
    then panic! "Message too long!"
    else x ++ (0x80 :: zeroes) ++ UInt64.toUInt8BE (UInt64.ofNat (l * 8))

def σ₀ (x : UInt32) : UInt32 := rotr  7 x ^^^ rotr 18 x ^^^ shr  3 x
def σ₁ (x : UInt32) : UInt32 := rotr 17 x ^^^ rotr 19 x ^^^ shr 10 x

def w (m : Vector UInt32 16) (t : Fin 64) : UInt32 :=
  if t < 16
    then m[Fin.ofNat 16 t]
    else σ₁ (w m (t - 2)) + w m (t - 7) + σ₀ (w m (t - 15)) + w m (t - 16)
  termination_by t

def ch  (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def E₀  (x     : UInt32) : UInt32 := rotr  2 x ^^^ rotr 13 x ^^^ rotr 22 x
def E₁  (x     : UInt32) : UInt32 := rotr  6 x ^^^ rotr 11 x ^^^ rotr 25 x

def hashLoop (m : Vector UInt32 16) (v : Vector UInt32 8) (t : Fin 64) : Vector UInt32 8 :=
  let w'                       := w m
  let (a, b, c, d, e, f, g, h) := (v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7])
  let t₁                       := h + E₁ e + ch e f g + k[t] + w' t
  let t₂                       := E₀ a + maj a b c
  let (h, g, f, e, d, c, b, a) := (g, f, e, d + t₁, c, b, a, t₁ + t₂)
  let v'                       := #v[ a, b, c, d, e, f, g, h ]
  if t < 63
    then hashLoop m v' (t + 1)
    else v'
  termination_by (63 - t)

def processChunks (v : Vector UInt32 8) (x : List UInt8) : Vector UInt32 8 :=
  if List.length x = 0
    then v
    else
      let x'    := List.drop 64 x
      let chunk := List.toArray (UInt32.listOfUInt8 (List.take 64 x))
      if harray_size : Array.size chunk = 16
        then let m  := Vector.mk chunk harray_size
             let h  := hashLoop m v 0
             let v' := h + v
             processChunks v' x'
        else unreachable!
  termination_by (List.length x)
  decreasing_by simp; omega

def initial : Vector UInt32 8 := #v[ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

def hashMessage (x : List UInt8) : Vector UInt32 8 :=
  let padded := padMessage x
  processChunks initial padded

def hash (x : String) : String :=
  let message := String.toByteList x
  let hashed  := hashMessage message
  uint32ListToHex (Vector.toList hashed)

end Internal

export Internal
  (
    hashMessage
    hash
  )

end Cryptograph.Sha2.Sha256
