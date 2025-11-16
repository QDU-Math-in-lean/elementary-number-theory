import Mathlib.FieldTheory.Finite.Basic

namespace EulerTheorem

open ZMod

@[inherit_doc]
scoped notation "φ" => Nat.totient

-- # Chapter 3 Congruences

-- ## 3.3 Euler's Theorem

-- ### Theorem 3.2 (Euler's Theorem)

/- If a, m ∈Nare coprime, then aφ(m) ≡1 (mod m) -/
theorem Nat.ModEq.pow_totient {x n : ℕ} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  let x' : Units (ZMod n) := ZMod.unitOfCoprime _ h
  have := ZMod.pow_totient x'
  apply_fun ((fun (x : Units (ZMod n)) => (x : ZMod n)) : Units (ZMod n) → ZMod n) at this
  simpa only [Nat.succ_eq_add_one, Nat.cast_pow, Units.val_one, Nat.cast_one,
    coe_unitOfCoprime, Units.val_pow_eq_pow_val]


end EulerTheorem
