import Cryptograph.Ed25519.Point
import Cryptograph.Sha2.Sha512

namespace Cryptograph.Ed25519.Signature

/-! ## Ed25519 Signature Verification-/

open Cryptograph.Ed25519.Point
open Cryptograph.Ed25519.Point.EdPoint (curveOrder)
open Cryptograph.Ed25519.Field
open Cryptograph.Sha2.Sha512

-- Convert bytes (little-endian) to Nat
def bytesToNat (bytes : ByteArray) : Nat :=
  (List.range bytes.size).foldr (λ i acc => bytes[i]!.toNat + acc * 256) 0

-- Reduce a 512-bit hash to a scalar modulo L (little-endian bytes)
def reduceModL (hash : ByteArray) : Nat :=
  bytesToNat hash % curveOrder

-- Verify Ed25519 signature
-- Returns true if signature is valid
def verify (publicKey : ByteArray) (message : ByteArray) (signature : ByteArray) : Bool :=
  -- Check lengths
  if publicKey.size != 32 then false
  else if signature.size != 64 then false
  else
    -- Split signature into R (32 bytes) and s (32 bytes)
    let rBytes := signature.extract 0 32
    let sBytes := signature.extract 32 64

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
        if Nat.ble curveOrder s then false
        else
          -- Compute hash: h = SHA-512(R || A || M)
          let hashInput := rBytes ++ publicKey ++ message
          let hashBytes := Internal.hashMessage hashInput

          -- Reduce hash modulo L
          let h := reduceModL hashBytes

          -- Compute left side: 8 * (s*B), cofactored equation as of RFC 8032
          let leftSide := 8 * s * EdPoint.basePoint

          -- Compute right side: 8 * (R + h*A), cofactored equation as of RFC 8032
          let rightSide := 8 * (r + h * a)

          -- Check if points are equal (in affine coordinates)
          let (lx, ly) := EdPoint.toAffine leftSide
          let (rx, ry) := EdPoint.toAffine rightSide

          lx == rx && ly == ry

end Cryptograph.Ed25519.Signature
