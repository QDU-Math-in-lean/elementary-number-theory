import MathmaticInElementaryNumberTh.Ch1_Greatest_Common_Divisor.Ch1_3_Greatest_Common_Divisor

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
theorem bezout_identity (m n : ℤ) (hm_not_zero : m ≠ 0) (hn_not_zero : n ≠ 0) :
    ∃ a b : ℤ , Nat.gcd (Int.natAbs m) (Int.natAbs n) = Int.natAbs (a * m + b * n) := by


end Bezout_Identity
