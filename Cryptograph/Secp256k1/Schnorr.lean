import Cryptograph.Secp256k1.Point
import Cryptograph.Sha2.Sha256

namespace Cryptograph.Secp256k1.Schnorr

/-! ## Schnorr Signature Verification for secp256k1 (BIP-340)-/

open Cryptograph.Secp256k1.Point
open Cryptograph.Secp256k1.Field
open Cryptograph.Sha2.Sha256

-- Curve order
def curveOrder : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

-- Convert bytes (big-endian) to Nat
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

-- Convert Nat to 32 bytes (big-endian)
partial def natToBytes32 (n : Nat) : List UInt8 :=
  let rec loop (n : Nat) (count : Nat) : List UInt8 :=
    if count = 0 then []
    else
      let byte := (n % 256).toUInt8
      loop (n / 256) (count - 1) ++ [byte]
  loop n 32

-- BIP-340 tagged hash: SHA256(SHA256(tag) || SHA256(tag) || msg)
def taggedHash (tag : String) (msg : List UInt8) : List UInt8 :=
  let tagBytes := tag.toUTF8.toList
  let tagHashVec := hashMessage tagBytes
  let tagHash := Vector.toList tagHashVec |>.flatMap Cryptograph.Integer.UInt32.toUInt8BE

  -- Double the tag hash and append message
  let input := tagHash ++ tagHash ++ msg
  let hashVec := hashMessage input
  Vector.toList hashVec |>.flatMap Cryptograph.Integer.UInt32.toUInt8BE

-- Lift x-coordinate to point (assumes even y)
def liftX (xBytes : List UInt8) : Option Secp256k1Point :=
  if xBytes.length ≠ 32 then none
  else
    -- BIP-340: reject if x ≥ p (raw integer must be a valid field element)
    let xNat := bytesToNat xBytes
    if xNat ≥ p then none
    else
    let x := Fp.ofNat xNat

    -- Compute y² = x³ + 7
    let yy := x^3 + 7

    -- Compute y = yy^((p+1)/4) (works because p ≡ 3 mod 4)
    let y := yy ^ ((p + 1) / 4)

    -- Check if y² = yy
    if y^2 ≠ yy then none
    else
      -- Choose even y
      let y := if y.val % 2 = 0 then y else -y
      some (Secp256k1Point.fromAffine x y)

-- Check if point has even y coordinate
def hasEvenY (p : Secp256k1Point) : Bool :=
  match Secp256k1Point.toAffine p with
  | none => false
  | some (_, y) => y.val % 2 = 0

-- Verify BIP-340 Schnorr signature
def verify (publicKey : List UInt8) (message : List UInt8) (signature : List UInt8) : Bool :=
  -- Check lengths
  if publicKey.length ≠ 32 then false
  else if signature.length ≠ 64 then false
  else
    -- Parse signature: r (32 bytes) || s (32 bytes)
    let rBytes := signature.take 32
    let sBytes := signature.drop 32
    let r := bytesToNat rBytes
    let s := bytesToNat sBytes

    -- Check r < p and s < n
    if r ≥ p || s ≥ curveOrder then false
    else
      -- Lift public key (x-only, even y)
      match liftX publicKey with
      | none => false
      | some pubKey =>
        -- Compute challenge e = H(r || pubkey || msg) mod n
        let eBytes := taggedHash "BIP0340/challenge" (rBytes ++ publicKey ++ message)
        let e := bytesToNat eBytes % curveOrder

        -- Compute R = s*G - e*P
        let sG := s * Secp256k1Point.basePoint
        let eP := e * pubKey
        let R := sG + (-eP)

        -- Check that R has even y and R.x = r
        if not (hasEvenY R) then false
        else
          match Secp256k1Point.toAffine R with
          | none => false
          | some (rx, _) => rx.val = r

end Cryptograph.Secp256k1.Schnorr
