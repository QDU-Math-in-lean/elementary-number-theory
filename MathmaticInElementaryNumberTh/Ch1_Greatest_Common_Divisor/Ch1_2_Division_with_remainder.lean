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

#check Int.ediv_emod_unique
#check Int.ediv_emod_unique'
theorem Int.ediv_emod_unique'' {a b r q : ℤ} (hb : b ≠ 0) :
    a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < |b| := by
    have hcases := lt_or_gt_of_ne hb
    cases hcases with
    | inl hneg =>
        have h : a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < -b := by
            exact Int.ediv_emod_unique' hneg
        -- 把表达式中的 `-b` 换成 `|b|`
        have habs : |b| = -b := by
            rw [abs_of_neg hneg]
        omega
    | inr hpos =>
        have h : a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < b := by
            exact Int.ediv_emod_unique hpos
        -- 把表达式中的 `b` 换成 `|b|`
        have habs : |b| = b := by
            rw [abs_of_pos hpos]
        omega

/-- For m, n ∈ ℤ with m ≠ 0, there exists a unique pair of integers q and r such that
    n = qm + r and 0 ≤ r < |m|.
    Here q = ⌊n/m⌋is called the quotient, and r is called the remainder.
-/
theorem int_division_with_remainder (n m : ℤ) (hm : m ≠ 0) :
    ∃ q : ℤ , ∃ r : ℤ , n = q * m + r ∧ 0 ≤ r ∧ r < |m| := by
    have hm_lt_zero : |m| > 0 := by
        simp
        exact hm
    let q := n / m
    let r := n % m
    have hq : n / m = q := by
        rfl
    have hr :n % m = r := by
        rfl
    have ediv_emod_unique :
        n / m = q ∧ n % m = r ↔ r + m * q = n ∧ 0 ≤ r ∧ r < |m| := by
        exact Int.ediv_emod_unique'' hm
    use q
    use r
    rw [hq] at ediv_emod_unique
    rw [hr] at ediv_emod_unique
    simp at ediv_emod_unique
    grind

end Division_with_remainder
