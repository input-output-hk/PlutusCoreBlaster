import Cryptograph.Integer

namespace Cryptograph.Ed25519.Field

/-! ## Field Arithmetic for Curve25519-/

-- The Curve25519 prime: 2^255 - 19
def p : Nat := 2^255 - 19

-- Field element: Nat modulo p wrapped in a structure
structure Fp where
  val : Nat
  deriving BEq, DecidableEq, Repr

-- Enable numeric literal syntax for Fp
instance : OfNat Fp n := ⟨⟨n % p⟩⟩

namespace Fp

-- Zero element
def zero : Fp := ⟨0⟩

-- One element
def one : Fp := ⟨1⟩

-- Normalize to range [0, p)
def normalize (n : Nat) : Fp :=
  ⟨n % p⟩

-- Convert from Nat (with modular reduction)
def ofNat (n : Nat) : Fp :=
  normalize n

-- Convert from Int (with modular reduction)
def ofInt (z : Int) : Fp :=
  let n := z % (p : Int)
  let n := if n < 0 then n + p else n
  normalize n.toNat

-- Addition modulo p
def add (a b : Fp) : Fp :=
  normalize (a.val + b.val)

instance : Add Fp := ⟨add⟩

-- Subtraction modulo p
def sub (a b : Fp) : Fp :=
  if a.val ≥ b.val then normalize (a.val - b.val)
  else normalize (p + a.val - b.val)

instance : Sub Fp := ⟨sub⟩

-- Negation modulo p
def neg (a : Fp) : Fp :=
  if a.val = 0 then ⟨0⟩ else normalize (p - a.val)

instance : Neg Fp := ⟨neg⟩

-- Multiplication modulo p
def mul (a b : Fp) : Fp :=
  normalize (a.val * b.val)

instance : Mul Fp := ⟨mul⟩

-- Squaring (optimized multiplication by self)
def square (a : Fp) : Fp :=
  normalize (a.val * a.val)

-- Power by natural number (using binary exponentiation)
def pow (a : Fp) (n : Nat) : Fp :=
  if n = 0 then one
  else if n = 1 then a
  else
    let half := pow a (n / 2)
    let squared := square half
    if n % 2 = 0 then squared else mul squared a
termination_by n

instance : HPow Fp Nat Fp := ⟨pow⟩

-- Modular inverse using Fermat's little theorem: a^(p-2) ≡ a^(-1) (mod p)
def inv (a : Fp) : Fp :=
  pow a (p - 2)

instance : Inv Fp := ⟨inv⟩

-- Division: a / b = a * b^(-1)
def div (a b : Fp) : Fp :=
  mul a (inv b)

instance : Div Fp := ⟨div⟩

-- Convert from bytes (little-endian, 32 bytes)
def fromBytesLE (bytes : ByteArray) : Option Fp :=
  let n := (List.range bytes.size).foldr (λ i acc => bytes[i]!.toNat + acc * 256) 0
  if n < p
    then some ⟨n⟩
    else none

-- Convert to bytes (little-endian, 32 bytes)
def toBytesLE (a : Fp) : ByteArray :=
  let rec loop (acc : ByteArray) (n : Nat) (count : Nat) : ByteArray :=
    if count = 0 then acc
    else loop (acc.push (n % 256).toUInt8) (n / 256) (count - 1)
  loop ByteArray.empty a.val 32

end Fp

end Cryptograph.Ed25519.Field
