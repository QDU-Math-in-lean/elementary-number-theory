import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic

-- 禁用未使用变量警告
-- set_option linter.unusedVariables false

open Nat

open Finset

/-- Euclid's Lemma: For a prime number `p`, if `p ∣ m * n` with `m, n ∈ ℤ`, then `p ∣ m` or `p ∣ n`. -/
lemma euclid_lemma {p m n : ℤ} (hp : Nat.Prime p.natAbs) (hpmn : p ∣ m * n) : p ∣ m ∨ p ∣ n := by
  by_cases hpm : p ∣ m
  · left; exact hpm
  · right
    have h_gcd : Int.gcd p m = 1 := by
      rw [Int.gcd_eq_natAbs, Nat.gcd_eq_one_iff_coprime]
      exact Nat.coprime_of_dvd' hpm hp.coprime_iff_not_dvd.2
    obtain ⟨a, b, hab⟩ := Int.exists_gcd_eq_one h_gcd
    rw [← hab] at hpmn
    exact dvd_trans (dvd_add (dvd_mul_of_dvd_left hpmn a) (dvd_mul_of_dvd_right hpmn b)) hpmn

/-- Example: Since `3` is a prime number and `3` divides `45 = 5 * 9`, then `3` must divide either `5` or `9`. -/
example : (3 : ℤ) ∣ 45 → (3 : ℤ) ∣ 5 ∨ (3 : ℤ) ∣ 9 :=
  euclid_lemma (by norm_num) (by norm_num)

/-- Euclid's Theorem: There are infinitely many prime numbers. -/
theorem euclid_theorem : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n := by
  intro n
  let m := Nat.factorial n + 1
  have h : ∃ p, Nat.Prime p ∧ p ∣ m := Nat.exists_prime_and_dvd m (Nat.succ_pos _)
  obtain ⟨p, hp_prime, hp_dvd⟩ := h
  use p
  constructor
  · exact hp_prime
  · by_contra h_le
    have h_dvd_fact : p ∣ Nat.factorial n := Nat.dvd_factorial (Nat.le_of_not_gt h_le) hp_prime.pos
    have h_contra : p ∣ 1 := Nat.dvd_sub' hp_dvd h_dvd_fact
    exact Nat.Prime.not_dvd_one hp_prime h_contra

/-- Prime Number Theorem: `π(x) ∼ x / log x` as `x → +∞`. -/
-- Note: This is a placeholder for the actual Prime Number Theorem, which requires advanced mathematics.
axiom prime_number_theorem : ∀ x : ℝ, x ≥ 2 → (π x) / (x / Real.log x) → 1 as x → ∞
