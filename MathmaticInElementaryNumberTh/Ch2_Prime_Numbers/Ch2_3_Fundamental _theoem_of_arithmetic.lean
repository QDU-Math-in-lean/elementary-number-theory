import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.Prime
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Subperm

-- 禁用未使用变量警告
-- set_option linter.unusedVariables false

open Nat

open Bool Subtype

open List


-- # Chapter 2 Prime Numbers

-- ## 2.3 Fundamental Theorem of Arithmetic

namespace Fundamental_Theorem_of_Arithmetic

-- ### Theorem 2.3 (Fundamental Theorem of Arithmetic)

#check Nat.primeFactorsList_unique

/-- Any integer n ≥2 can be expressed uniquely (up to ordering) as a product of prime numbers:
  n = p1p2 ···pk,
  where each pi (i = 1, 2, . . . , k) is a prime number
-/
theorem primeFactorsList_unique {n : ℕ} {l : List ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, Nat.Prime p) :
    l ~ primeFactorsList n := by
  refine perm_of_prod_eq_prod ?_ ?_ ?_
  · rw [h₁]
    refine (prod_primeFactorsList ?_).symm
    rintro rfl
    rw [List.prod_eq_zero_iff] at h₁
    exact Nat.Prime.ne_zero (h₂ 0 h₁) rfl
  · simp_rw [← prime_iff]
    exact h₂
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_primeFactorsList

end Fundamental_Theorem_of_Arithmetic
