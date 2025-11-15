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

-- # Chapter 1 Greatest Common Divisor

-- ## 1.2 Division with remainder

namespace Division_with_remainder

-- ### Theorem 1.1 (Division with remainder)

-- For m, n ∈ ℤ with m ≠ 0, there exists a unique pair of integers q and r such that
-- n = qm + r and 0 ≤ r < |m|.
-- Here q = ⌊n/m⌋is called the quotient, and r is called the remainder.
#check Int.ediv_emod_unique
theorem int_division_with_remainder (n m : ℤ) (hm : m ≠ 0) :
    ∃ q : ℤ , ∃ r : ℤ , n = q * m + r ∧ 0 ≤ r ∧ r < |m| := by
    sorry
end Division_with_remainder
