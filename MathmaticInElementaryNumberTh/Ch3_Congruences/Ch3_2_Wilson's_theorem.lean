import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson

variable (p : ℕ) [Fact p.Prime]
variable {n : ℕ}

namespace WilsonTheorem
open ZMod

-- # Chapter 3 Congruences

-- ## 3.2 Wilson's Theorem

-- ### Theorem 3.1 (Wilson's Theorem)

/- A positive integer n > 1 is a prime if and only if (n −1)! + 1 ≡0 (mod n) -/
theorem prime_iff_fac_equiv_neg_one (h : n ≠ 1) : Nat.Prime n ↔ (Nat.factorial (n - 1) : ZMod n) = -1 := by
  refine ⟨fun h1 => ?_, fun h2 => Nat.prime_of_fac_equiv_neg_one h2 h⟩
  haveI := Fact.mk h1
  exact ZMod.wilsons_lemma n

/-- For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. -/
theorem prime_of_fac_equiv_neg_one (h : (Nat.factorial (n - 1) : ZMod n) = -1) (h1 : n ≠ 1) : Nat.Prime n := by
  rcases eq_or_ne n 0 with (rfl | h0)
  · norm_num at h
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩
  by_contra h2
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := Nat.exists_dvd_of_not_prime2 h1 h2
  have hm : m ∣ Nat.factorial (n - 1) := Nat.dvd_factorial (pos_of_gt hm2) (Nat.le_pred_of_lt hm3)
  refine hm2.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hm).mp (hm1.trans ?_)))
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, h, neg_add_cancel]

end WilsonTheorem
