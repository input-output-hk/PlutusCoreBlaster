import PlutusCore.Integer.Basic

namespace PlutusCore.Crypto.ExpMod

open PlutusCore.Integer

/-! ## Formalisation for PlutusCore Modular Exponentiation builtin function.

    Ref: plutus-core/src/PlutusCore/Crypto/ExpMod.hs
    Semantics:
      expModInteger b e m
        | m ≤ 0       → fail
        | m = 1       → 0
        | e ≥ 0       → b^e mod m  (non-negative, in [0, m-1])
        | e < 0       → if gcd(b mod m, m) = 1, compute modular inverse of b^(-e) mod m
                        else fail
-/

namespace Internal

-- Fast modular exponentiation: b^e mod m, for e ≥ 0 and m > 0.
-- Result is in [0, m-1]. Uses right-to-left binary method.
def powMod (b e m : Int) : Int :=
  if m = 1 then 0
  else
    let b' := ((b % m) + m) % m  -- normalise base to [0, m-1]
    let rec go (base acc : Int) (exp : Nat) : Int :=
      if exp = 0 then acc
      else
        let acc' := if exp % 2 = 1 then (acc * base) % m else acc
        go (base * base % m) acc' (exp / 2)
    termination_by exp
    go b' 1 e.toNat

-- Extended Euclidean algorithm: returns (g, s) such that g = gcd(a,b) and s*a ≡ g (mod b).
-- Termination: r.natAbs decreases at every step because, for E-division,
--   (a % b).natAbs < b.natAbs  (when b ≠ 0),
-- as captured by Int.natAbs_emod and the Nat.mod_lt bound.
set_option linter.unusedVariables false in
def extGcd (a b : Int) : Int × Int :=
  let rec go (old_r r old_s s : Int) : Int × Int :=
    if h : r = 0 then (old_r, old_s)
    else
      let q := old_r / r
      go r (old_r % r) s (old_s - q * s)
  termination_by r.natAbs
  decreasing_by
    have hna : 0 < r.natAbs := Int.natAbs_pos.mpr h
    rw [Int.natAbs_emod old_r h]
    by_cases hcond : 0 ≤ old_r ∨ r ∣ old_r
    · rw [if_pos hcond]; exact Nat.mod_lt _ hna
    · rw [if_neg hcond]
      have hndvd : ¬(r ∣ old_r) := fun hdvd => hcond (Or.inr hdvd)
      have hmod_ne : old_r.natAbs % r.natAbs ≠ 0 := fun h0 =>
        hndvd (Int.natAbs_dvd_natAbs.mp (Nat.dvd_of_mod_eq_zero h0))
      omega
  if b = 0 then (a, 1) else go a b 1 0

-- Modular inverse of a mod m (m > 1). Returns .ok x where x ∈ [0,m-1],
-- or .error if gcd(a,m) ≠ 1.
def modInverse (a m : Int) : Except String Int :=
  let (g, s) := extGcd (((a % m) + m) % m) m
  if g = 1 then .ok (((s % m) + m) % m)
  else .error "expModInteger: base has no modular inverse"

opaque expModInteger (b e m : Integer) : Except String Integer :=
  if m ≤ 0 then
    .error "expModInteger: modulus must be positive"
  else if m = 1 then
    .ok 0
  else if e ≥ 0 then
    .ok (powMod b e m)
  else
    -- negative exponent: compute (b^(-e) mod m)^(-1) mod m
    match modInverse b m with
    | .error msg => .error msg
    | .ok bInv   => .ok (powMod bInv (-e) m)

end Internal

export Internal (expModInteger)

end PlutusCore.Crypto.ExpMod
