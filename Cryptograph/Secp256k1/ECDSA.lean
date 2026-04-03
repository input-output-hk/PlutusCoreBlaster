import Cryptograph.Secp256k1.Point
import Cryptograph.Sha2.Sha256

namespace Cryptograph.Secp256k1.ECDSA

/-! ## ECDSA Signature Verification for secp256k1-/

open Cryptograph.Secp256k1.Point
open Cryptograph.Secp256k1.Field
open Cryptograph.Sha2.Sha256

-- Curve order (number of points)
-- n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
def curveOrder : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

-- Modular inverse modulo curve order
partial def invModN (a : Nat) : Nat :=
  let rec powModN (base : Nat) (exp : Nat) : Nat :=
    if exp = 0 then 1
    else if exp = 1 then base % curveOrder
    else
      let half := powModN base (exp / 2)
      let squared := (half * half) % curveOrder
      if exp % 2 = 0 then squared
      else (squared * base) % curveOrder
  powModN a (curveOrder - 2)

-- Convert bytes (big-endian) to Nat
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

-- Helper: verify with parsed point
def verifyWithPoint (q : Secp256k1Point) (r s : Nat) (message : List UInt8) : Bool :=
  -- message is already a 32-byte hash (per Plutus ECDSA spec)
  let h := bytesToNat message

  -- Compute u1 = h * s^-1 (mod n)
  let sInv := invModN s
  let u1 := (h * sInv) % curveOrder

  -- Compute u2 = r * s^-1 (mod n)
  let u2 := (r * sInv) % curveOrder

  -- Compute R = u1*G + u2*Q
  let point1 := Secp256k1Point.scalarMul u1 Secp256k1Point.basePoint
  let point2 := Secp256k1Point.scalarMul u2 q
  let pointR := Secp256k1Point.add point1 point2

  -- Extract x coordinate
  match Secp256k1Point.toAffine pointR with
  | none => false
  | some (x, _) =>
    -- Check if x (mod n) = r
    (x.val % curveOrder) = r

-- Verify ECDSA signature
def verify (publicKey : List UInt8) (message : List UInt8) (signature : List UInt8) : Bool :=
  -- Check signature length
  if signature.length ≠ 64 then false
  else
    -- Parse signature: r (32 bytes) || s (32 bytes)
    let rBytes := signature.take 32
    let sBytes := signature.drop 32
    let r := bytesToNat rBytes
    let s := bytesToNat sBytes

    -- Check r, s are in valid range [1, n-1] and low-s (s ≤ n/2)
    -- Note: r = 0, r ≥ n, s = 0, s ≥ n are handled as errors in Basic.lean
    if r = 0 || r ≥ curveOrder || s = 0 || s ≥ curveOrder then false
    -- Plutus enforces low-s: reject signatures with s > n/2
    else if s > curveOrder / 2 then false
    else
      -- Parse public key
      match Secp256k1Point.decompress publicKey with
      | none =>
        -- Try uncompressed format (0x04 || x || y)
        if publicKey.length ≠ 65 || publicKey[0]! ≠ 0x04 then false
        else
          let xBytes := publicKey.toArray[1:33].toList
          let yBytes := publicKey.toArray[33:65].toList
          let x := Fp.fromBytesBE xBytes
          let y := Fp.fromBytesBE yBytes
          let q := Secp256k1Point.fromAffine x y
          verifyWithPoint q r s message
      | some q => verifyWithPoint q r s message

end Cryptograph.Secp256k1.ECDSA
