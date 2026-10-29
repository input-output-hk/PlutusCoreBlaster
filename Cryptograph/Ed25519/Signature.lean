import Cryptograph.Ed25519.Point
import Cryptograph.Sha2.Sha512

namespace Cryptograph.Ed25519.Signature

/-! ## Ed25519 Signature Verification-/

open Cryptograph.Ed25519.Point
open Cryptograph.Ed25519.Point.EdPoint (curveOrder)
open Cryptograph.Ed25519.Field
open Cryptograph.Sha2.Sha512

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
  if publicKey.length != 32 then false
  else if signature.length != 64 then false
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
        -- Match libsodium/Cardano's single-signature verification: reject small-order
        -- keys/nonces, then check the uncofactored equation. Cofactor multiplication
        -- would accept e.g. the identity key with an identity nonce and scalar zero.
        if EdPoint.isZero ((8 : Nat) * a) || EdPoint.isZero ((8 : Nat) * r) then false
        else
        -- Decode s as scalar (little-endian)
        let s := bytesToNat sBytes

        -- Check s < L (curve order)
        if Nat.ble curveOrder s then false
        else
          -- Compute hash: h = SHA-512(R || A || M)
          let hashInput  := rBytes ++ publicKey ++ message
          let hashOutput := Internal.hashMessage hashInput
          let hashBytes  := hashOutput.flatMap Cryptograph.Integer.UInt64.toUInt8BE

          -- Reduce hash modulo L
          let h := reduceModL hashBytes

          -- Compute left side: s*B
          let leftSide := s * EdPoint.basePoint

          -- Compute right side: R + h*A
          let rightSide := r + h * a

          -- Check if points are equal (in affine coordinates)
          let (lx, ly) := EdPoint.toAffine leftSide
          let (rx, ry) := EdPoint.toAffine rightSide

          lx == rx && ly == ry

end Cryptograph.Ed25519.Signature
