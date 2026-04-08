import Cryptograph.Ed25519.Point
import Cryptograph.Sha2.Sha512

namespace Cryptograph.Ed25519.Signature

/-! ## Ed25519 Signature Verification-/

open Cryptograph.Ed25519.Point
open Cryptograph.Ed25519.Field
open Cryptograph.Sha2.Sha512

-- Curve order (number of points on the curve)
-- L = 2^252 + 27742317777372353535851937790883648493
def curveOrder : Nat := 2^252 + 27742317777372353535851937790883648493

-- Convert bytes (little-endian) to Nat
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldr (fun b acc => b.toNat + acc * 256) 0

-- Reduce a 512-bit hash to a scalar modulo L (little-endian bytes)
def reduceModL (hash : List UInt8) : Nat :=
  bytesToNat hash % curveOrder

-- Verify Ed25519 signature
-- Returns true if signature is valid
def verify (publicKey : List UInt8) (message : List UInt8) (signature : List UInt8) : Bool :=
  -- Check lengths
  if publicKey.length ≠ 32 then false
  else if signature.length ≠ 64 then false
  else
    -- Split signature into R (32 bytes) and s (32 bytes)
    let rBytes := signature.take 32
    let sBytes := signature.drop 32

    -- Decode public key A
    match EdPoint.decompress publicKey with
    | none => false
    | some a =>
      -- Decode R
      match EdPoint.decompress rBytes with
      | none => false
      | some r =>
        -- Decode s as scalar (little-endian)
        let s := bytesToNat sBytes

        -- Check s < L (curve order)
        if s ≥ curveOrder then false
        else
          -- Compute hash: h = SHA-512(R || A || M)
          let hashInput := rBytes ++ publicKey ++ message
          let hashOutput := Internal.hashMessage hashInput
          let hashBytes := hashOutput.flatMap Cryptograph.Integer.UInt64.toUInt8BE

          -- Reduce hash modulo L
          let h := reduceModL hashBytes

          -- Compute left side: s*B
          let leftSide := EdPoint.scalarMul s EdPoint.basePoint

          -- Compute right side: R + h*A
          let hA := EdPoint.scalarMul h a
          let rightSide := EdPoint.add r hA

          -- Check if points are equal (in affine coordinates)
          let (lx, ly) := EdPoint.toAffine leftSide
          let (rx, ry) := EdPoint.toAffine rightSide

          lx == rx && ly == ry

end Cryptograph.Ed25519.Signature
