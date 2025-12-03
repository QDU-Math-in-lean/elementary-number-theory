import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- # Chapter 4 Linear Congruence Equation

-- ## Basic Examples of Linear Congruence Equations and the Chinese Remainder Theorem

/-
- 线性同余方程

关键结论：方程 ax ≡ b (mod m) 有解当且仅当 gcd(a, m) | b。

- 示例：4x ≡ 6 (mod 10)

因为 gcd(4, 10) = 2，且 2 | 6，所以方程有解。
将方程两边除以 2 得：2x ≡ 3 (mod 5)。
在模 5 下，2 的逆元是 3（因为 2 × 3 = 6 ≡ 1 (mod 5)）。
所以 x ≡ 3 × 3 ≡ 9 ≡ 4 (mod 5)。
因此在模 10 下的解是 x ≡ 4 (mod 10) 和 x ≡ 9 (mod 10)。

-/

-- 验证 x = 4 是一个解
example : (4 : ZMod 10) * (4 : ZMod 10) = (6 : ZMod 10) := by
  decide

-- 验证 x = 9 也是一个解
example : (4 : ZMod 10) * (9 : ZMod 10) = (6 : ZMod 10) := by
  decide

/-
一般性定理：方程 ax ≡ b (mod m) 有解当且仅当 gcd(a, m) | b。
完整的一般性证明需要 Bézout 引理和模算术的逆元理论。
这里我们给出具体例子的构造性证明。
-/

-- 证明方程 4x ≡ 6 (mod 10) 有解 (因为 gcd(4,10)=2 且 2|6)
example : ∃ x : ZMod 10, (4 : ZMod 10) * x = (6 : ZMod 10) := by
  use (4 : ZMod 10)
  decide

-- 另一个例子：2x ≡ 4 (mod 6) 有解（因为 gcd(2,6)=2 且 2|4）
example : ∃ x : ZMod 6, (2 : ZMod 6) * x = (4 : ZMod 6) := by
  use (2 : ZMod 6)
  norm_num

-- 反例：2x ≡ 3 (mod 6) 无解（因为 gcd(2,6)=2 但 2∤3）
example : ¬∃ x : ZMod 6, (2 : ZMod 6) * x = (3 : ZMod 6) := by
  decide

/-!
## 中国剩余定理（Chinese Remainder Theorem）

当模数互质时，可以同时解多个同余方程组成的方程组。

### 例子：解方程组
```
x ≡ 2 (mod 3)
x ≡ 3 (mod 4)
```

因为 gcd(3, 4) = 1，根据中国剩余定理，存在唯一解 x ≡ a (mod 12)。

**解法：**
1. 从第一个方程：x = 3k + 2（对某个整数 k）
2. 代入第二个方程：3k + 2 ≡ 3 (mod 4)
3. 即：3k ≡ 1 (mod 4)
4. 因为 3 × 3 = 9 ≡ 1 (mod 4)，所以 3 的逆元是 3
5. 因此：k ≡ 3 × 1 ≡ 3 (mod 4)，即 k = 4m + 3
6. 代回：x = 3(4m + 3) + 2 = 12m + 9 + 2 = 12m + 11
7. 所以：x ≡ 11 (mod 12)
-/

-- 验证 11 在模 3 下余 2
example : 11 % 3 = 2 := by norm_num

-- 验证 11 在模 4 下余 3
example : 11 % 4 = 3 := by norm_num

-- 证明任何满足两个条件的数在模 12 下都等于 11
example (x : ℤ) (h3 : x % 3 = 2) (h4 : x % 4 = 3) : x % 12 = 11 := by
  -- 使用中国剩余定理
  omega

-- 验证解的存在性和其他例子
example : 11 % 3 = 2 ∧ 11 % 4 = 3 := by norm_num
example : 23 % 3 = 2 ∧ 23 % 4 = 3 := by norm_num
example : 35 % 3 = 2 ∧ 35 % 4 = 3 := by norm_num
example : (-1 : ℤ) % 3 = 2 ∧ (-1 : ℤ) % 4 = 3 := by norm_num
