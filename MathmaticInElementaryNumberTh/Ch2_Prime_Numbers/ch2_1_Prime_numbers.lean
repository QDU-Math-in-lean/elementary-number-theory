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

-- any n , n > 2 ,n exists prime divisors
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

-- any composite number n has a prime divisor p ≤ √n
#check Nat.prime_def_le_sqrt
theorem composite_prime_divisor_bound
(n : ℕ) (hn : n ≥ 2) (h_composite : ¬Nat.Prime n) :
  ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p ≤ Nat.sqrt n := by
  have h_ne_one : n ≠ 1 := by
    linarith

  sorry


-- -- if n has no prime divisors, then n = 1
theorem uniqueness_of_one_in_prime_divisibility (n : ℕ) :
  (∀ p : ℕ, Nat.Prime p → ¬(p ∣ n)) → n = 1 := by
  intro h
  -- 情形 1: n = 0，任意素数整除 0，与假设矛盾
  by_cases hn0 : n = 0
  · have : (2 : ℕ) ∣ n := by rw [hn0]; simp
    specialize h 2 Nat.prime_two
    exact (h this).elim
  -- 情形 2: n = 1，直接成立
  by_cases hn1 : n = 1
  · exact hn1
  -- 情形 3: n ≠ 0 且 n ≠ 1，则 n ≥ 2，可用已证引理得到素数因子
  have h_ge_two : n ≥ 2 := by
    cases n
    · exact (hn0 rfl).elim
    case succ n' =>
      cases n'
      · exact (hn1 rfl).elim
      · linarith
  obtain ⟨p, hp_prime, hp_dvd⟩ := le_two_exists_prime_divisors n h_ge_two
  specialize h p hp_prime
  exact (h hp_dvd).elim
