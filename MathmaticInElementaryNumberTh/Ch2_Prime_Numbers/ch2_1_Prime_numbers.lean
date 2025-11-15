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

open Int

open Finset

theorem le_two_exists_prime_divisors (n : ℕ) (hn : n ≥ 2) :
  ∃ p : ℕ, Nat.Prime p ∧ p ∣ n := by
  have h_ne_one : n ≠ 1 := by
    linarith
  let p := Nat.minFac n
  have h_prime : Nat.Prime p := by
    exact Nat.minFac_prime h_ne_one
  use p
  constructor
  · exact h_prime
  · exact Nat.minFac_dvd n

theorem composite_prime_divisor_bound (n : ℕ) (hn : n ≥ 2) (h_composite : ¬Nat.Prime n) :
  ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p ≤ Nat.sqrt n := by
  have h_ne_one : n ≠ 1 := by
    linarith

  sorry


theorem uniqueness_of_one_in_prime_divisibility (n : ℕ) :
  (∀ p : ℕ, Nat.Prime p → ¬(p ∣ n)) → n = 1 := by
  contrapose!
  intro h_ne_one
  have h_ge_two : n ≥ 2 := by
    by_contra not_h_le_two
    have h_le_two : n ≤ 1 := by
      linarith
    case n with
    | zero => linarith
    | succ zero => linarith

  obtain ⟨p, h_prime, h_dvd⟩ := by
    exact le_two_exists_prime_divisors n h_ge_two
  exact ⟨p, h_prime, h_dvd⟩
