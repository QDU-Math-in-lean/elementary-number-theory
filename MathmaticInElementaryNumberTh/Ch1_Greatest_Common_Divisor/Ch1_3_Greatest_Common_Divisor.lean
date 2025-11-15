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

-- # Chapter 1 Greatest Common Divisor

-- ## 1.3 Greatest Common Divisor

namespace Greatest_Common_Divisor

variable (n : ℤ)


-- ### Definition 1.2 (Divisor)

-- If d|n, then d is called a divisor of n.
-- 遍历整数区间 [-|n|, |n|] 中的所有非零整数 d，
-- 并筛选出那些满足 d|n 的整数 d，最终得到的集合
-- 应该注意的是,讲义中所定义的 e_dvd 还包含了一个条件是 除数非0, 而mathlib中并没有此限制
def divisors (n : ℤ) : Finset ℤ :=
  (Icc (-(n.natAbs : ℤ)) (n.natAbs : ℤ)).filter (λ d => d ≠ 0 ∧ d ∣ n)


-- ### Definition 1.3 (Common Divisor)

-- For m, n ∈ Z, if an integer d satisfies d|m and d|n,
-- then d is called a common divisor of m and n
def common_divisors (m n : ℤ) : Finset ℤ :=
  (Icc 1 (min m.natAbs n.natAbs : ℤ)).filter (λ d => d ≠ 0 ∧ d ∣ m ∧ d ∣ n)

-- ### Definition 1.4 (Greatest Common Divisor)

--For m, n ∈ Z, not both zero, the greatest common divisor of m and n,
-- denoted by gcd(m, n), is the largest positive common divisor of m and n.
def gcd (m n : ℤ) : ℤ := Int.gcd m n -- from mathlib

-- 0 ≤ gcd m n
lemma gcd_nonneg (m n : ℤ) : 0 ≤ gcd m n := by
  rw [gcd] -- 展开为 Int.gcd m n
  simp


-- ### Proposition 1.5.1 (The greatest common divisor is commutative)

-- gcd(m, n) = gcd(n, m)
theorem gcd_comm (m n : ℤ) : gcd m n = gcd n m := by
  have h1 : m.gcd n = n.gcd m := by -- 困难在于我自己定义的 gcd与 mathlib 中的定义 的区别
    exact Int.gcd_comm m n -- from mathlib
  have h2 : gcd m n = m.gcd n := by
    rfl
  have h3 : gcd n m = n.gcd m := by
    rfl
  rw [h2, h1, h3]


-- ### Proposition 1.5.2 (The greatest common divisor divides both numbers)

-- If m|n, 0 ≤ m, then gcd(m, n) = m
theorem gcd_eq_left (m n : ℤ) (hmn : m ∣ n) (hm_le_0: 0 ≤ m): gcd m n = m := by
  exact Int.gcd_eq_left hm_le_0 hmn  -- from mathlib


-- ### Proposition 1.5.3 (The greatest common divisor divides both numbers)

-- In particular, gcd(m, 0) = m for any m ∈ Z with m > 0
theorem gcd_eq_zero (m : ℤ) : gcd m 0 = Int.natAbs m := by
  have h1 : Int.natAbs m = m.natAbs := by rfl
  have h2 : m ∣ 0 := by
    exact Int.dvd_zero m
  have h3 : gcd m 0 = m.gcd 0:= by
    rfl
  rw [h3]
  simp

end Greatest_Common_Divisor
