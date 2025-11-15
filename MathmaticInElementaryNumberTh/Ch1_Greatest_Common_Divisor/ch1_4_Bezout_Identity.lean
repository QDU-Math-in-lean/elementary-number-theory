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
#check exists_gcd_eq_mul_add_mul
#check Int.gcd_dvd_iff
theorem bezout_identity (m n : ℕ) :
    ∃ a b : ℤ , Nat.gcd m n = a * m + b * n := by
    -- 将 m, n 视为整数
    let m' : ℤ := ↑m
    let n' : ℤ := ↑n
    -- 使用整数上的 Bézout 恒等式 Int.gcd_eq_gcd_ab
    have h_bezout : m'.gcd n' = Int.gcdA m' n' * m' + Int.gcdB m' n' * n' := by
        simp [Int.gcd_eq_gcd_ab m' n']
        grind
    -- 建立 Nat.gcd 和 Int.gcd 的联系
    have h_gcd_eq : Nat.gcd m n = m'.gcd n' := by
        simp [m', n']
    -- 构造系数
    use Int.gcdA m' n', Int.gcdB m' n'
    -- 证明等式
    rw [h_gcd_eq, h_bezout]

end Bezout_Identity
