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
def bytesToNat (bytes : ByteArray) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

-- BIP-340 tagged hash: SHA256(SHA256(tag) || SHA256(tag) || msg)
def taggedHash (tag : String) (msg : ByteArray) : ByteArray :=
  let tagHash := hashMessage tag.toUTF8
  -- Double the tag hash and append message
  hashMessage (tagHash ++ tagHash ++ msg)

-- Lift x-coordinate to point (assumes even y)
def liftX (xBytes : ByteArray) : Option Secp256k1Point :=
  if xBytes.size ≠ 32 then none
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
  | none        => false
  | some (_, y) => y.val % 2 == 0

-- Verify BIP-340 Schnorr signature
def verify (publicKey : ByteArray) (message : ByteArray) (signature : ByteArray) : Bool :=
  -- Check lengths
  if publicKey.size ≠ 32 then false
  else if signature.size ≠ 64 then false
  else
    -- Parse signature: r (32 bytes) || s (32 bytes)
    let rBytes := signature.extract 0 32
    let sBytes := signature.extract 32 64
    let r := bytesToNat rBytes
    let s := bytesToNat sBytes

    -- Check r < p and s < n
    if Nat.ble p r || Nat.ble curveOrder s then false
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
          | none         => false
          | some (rx, _) => rx.val == r

end Cryptograph.Secp256k1.Schnorr
