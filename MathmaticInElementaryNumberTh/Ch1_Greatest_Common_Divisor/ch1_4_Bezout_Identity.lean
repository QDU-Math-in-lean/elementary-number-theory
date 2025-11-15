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

-- ## 1.4 Bézout's Identity

namespace Bezout_Identity

-- ### Theorem 1.2 (Bézout’s Identity)

-- For m, n ∈ Z, not both zero,
-- there exist a, b ∈ Z,
-- such that gcd(m, n) = am + bn
theorem bezout_identity (m n : ℕ) (hm_not_zero : m ≠ 0) (hn_not_zero : n ≠ 0) :
    ∃ a b : ℤ , Nat.gcd m n = a * m + b * n := by
    revert n
    apply Nat.strong_induction_on m
    sorry

end Bezout_Identity
