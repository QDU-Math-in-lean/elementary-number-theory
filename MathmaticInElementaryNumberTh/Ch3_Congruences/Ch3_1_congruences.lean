import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic

variable {m n a b c d : ℤ}
namespace congruences

-- # Chapter 3 Congruences

-- ## 3.1 Congruences

-- ### Definition 3.1 (Congruences)

--666
/-Let a, b ∈Zand m be a non-zero integer. If there exists k ∈Zsuch that a = b + km,
then we say a andb are congruent (or a is congruent to b) modulo m, denoted by a ≡ b (mod m).
Here, m is called themodulus of the congruence.-/
theorem modEq_iff_add_fac {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t := by
  rw [Int.modEq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'


-- ### proposition 3.1 (Modulus Scalling Property)

--666
/- Let k be a non-zero integer, then ka ≡kb (mod km) if and only if a ≡b (mod m)-/
theorem mul_right_cancel_iff' (hc : c ≠ 0) :
    a * c ≡ b * c [ZMOD m * c] ↔ a ≡ b [ZMOD m] :=
  ⟨Int.ModEq.mul_right_cancel' hc, Int.ModEq.mul_right'⟩


--666
/- Let k be a non-zero integer, then ac ≡bc (mod mc) if and only if a ≡b (mod m)-/
theorem mul_left_cancel_iff' (hc : c ≠ 0) :
    c * a ≡ c * b [ZMOD c * m] ↔ a ≡ b [ZMOD m] :=
  ⟨Int.ModEq.mul_left_cancel' hc, Int.ModEq.mul_left'⟩


-- ### proposition 3.2 (Fundamental Congruence Criterion)

--666
/- For a non-zero integer m, we have a ≡b (mod m) if and only if m |a −b-/
theorem modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a := by
  rw [Int.ModEq, eq_comm]
  simp [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]


-- ### proposition 3.3 (Congruence Modulo m as an Equivalence Relation)

--666
/- Let m be a non-zero integer. For any a, b, c ∈Z, the following properties hold:
(1) Reflexivity: a ≡a (mod m).
(2) Symmetry: If a ≡b (mod m), then b ≡a (mod m).
(3) Transitivity: If a ≡b (mod m) and b ≡c (mod m), then a ≡c (mod m)-/
theorem rfl : a ≡ a [ZMOD n] :=
  Int.ModEq.refl _
theorem symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] :=
  Int.ModEq.symm h
theorem trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] :=
  Int.ModEq.trans h1 h2


-- ### Proposition 3.4 (Congruence Preservation under Addition and Multiplication)

--666
/- Let m be a non-zero integer. We have the following statements:
If a1 ≡b1 (mod m) and a2 ≡b2 (mod m), then a1 + a2 ≡b1 + b2 (mod m).
If a1 ≡b1 (mod m) and a2 ≡b2 (mod m), then a1a2 ≡b1b2 (mod m).  -/
theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
  modEq_iff_dvd.2 <| by convert Int.dvd_add h₁.dvd h₂.dvd using 1; omega
theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] :=
  modEq_iff_dvd.2 <| by convert Int.dvd_sub h₁.dvd h₂.dvd using 1; omega
theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)


-- ### Collary 3.1 (Congruence Preservation under Scalling and Exponentiation)

--666
/- Let m be a non-zero integer. We have the following statements:
(i) If a ≡b (mod m), then ka ≡kb (mod m) for any k ∈Z.
(ii) If a ≡b (mod m), then al ≡bl (mod m) for any l ∈N.-/
theorem pow (m : ℕ) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] := by
  induction m with
  | zero => rfl
  | succ d hd => rw [pow_succ, pow_succ]; exact hd.mul h
theorem k_mul (k : ℤ) (h : a ≡ b [ZMOD n]) : k * a ≡ k * b [ZMOD n] :=
  h.mul_left k


-- ### Proposition 3.5 (Invertibility Criterion modulo m)

--666
/- Let a, m ∈Zwith m ̸= 0. Then a is invertible modulo m if and only if gcd(a, m) = 1.-/
theorem mod_coprime {a b : ℕ} (hab : Nat.Coprime a b) : ∃ y : ℤ, a * y ≡ 1 [ZMOD b] :=
  ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] :=
        Int.ModEq.symm <| Int.modEq_add_fac _ <| Int.ModEq.refl _
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd]; rfl
      ⟩


-- ### Proposition 3.6 (Cancellation Law for Congruences)

--666
/- If ka ≡kb (mod m) and gcd(k, m) = 1, then a ≡b (mod m).-/
theorem cancel_left_of_coprime {m  a b c : ℕ}(hmc : Nat.gcd m c = 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m] := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simp only [Nat.gcd_zero_left] at hmc
    simp only [hmc, one_mul, Nat.modEq_zero_iff] at h
    subst h
    rfl
  simpa [hmc] using h.cancel_left_div_gcd hm
theorem cancel_right_of_coprime {m  a b c : ℕ}(hmc : Nat.gcd m c = 1) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m] :=
  cancel_left_of_coprime hmc <| by simpa [mul_comm] using h


--666
/- If ka ≡kb (mod m), then a ≡b (mod m / gcd(m, k)).-/
theorem cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m]) : a ≡ b [ZMOD m / Int.gcd m c] :=
  Int.ModEq.cancel_right_div_gcd hm <| by simpa [mul_comm] using h
theorem cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m]) :
    a ≡ b [ZMOD m / Int.gcd m c] := by
  letI d := Int.gcd m c
  rw [modEq_iff_dvd] at h ⊢
  refine Int.dvd_of_dvd_mul_right_of_gcd_one (?_ : m / d ∣ c / d * (b - a)) ?_
  · rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (Int.gcd_dvd_right ..), Int.sub_mul]
    exact Int.ediv_dvd_ediv (Int.gcd_dvd_left ..) h
  · rw [Int.gcd_div (Int.gcd_dvd_left ..) (Int.gcd_dvd_right ..), Int.natAbs_natCast,
      Nat.div_self (Int.gcd_pos_of_ne_zero_left c hm.ne')]


end congruences
