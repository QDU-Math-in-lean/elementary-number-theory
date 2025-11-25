import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Prime.Int

namespace p_adic_valuation

variable {p : ℕ} [hp : Fact p.Prime]
@[inherit_doc] scoped infixl:70 " /. " => Rat.divInt
-- # Chapter 2 Prime Numbers

-- ## 2.4 p-adic valuation

-- ### Proposition 2.2 (Additivity of p-adic Valuation

--666
/- Let p be a prime, then for any m, n ∈N, we have vp(mn) = vp(m) + vp(n).-/
protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q * r) = padicValRat p q + padicValRat p r := by
  have : q * r = (q.num * r.num) /. (q.den * r.den) := by
    rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, Nat.cast_mul]
  have hq' : q.num /. q.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hr' : r.num /. r.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this]
  conv_rhs =>
    rw [← q.num_divInt_den, padicValRat.defn p hq', ← r.num_divInt_den, padicValRat.defn p hr']
  rw [multiplicity_mul hp', multiplicity_mul hp', Nat.cast_add, Nat.cast_add]
  · ring
  · simp [padicValRat.finite_int_prime_iff]
  · simp [padicValRat.finite_int_prime_iff, hq, hr]


--### Proposition 2.3 (Ultrametric Inequality)

--666
/- Let p be a prime, then for any m, n ∈N,
we havevp(m + n) ≥min (vp(m), vp(n)),with equality if vp(m) ̸= vp(n)-/
theorem min_le_padicValRat_add {q r : ℚ} (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact padicValRat.le_padicValRat_add_of_le hqr h)
  (fun h => by rw [min_eq_right h, add_comm]; exact padicValRat.le_padicValRat_add_of_le (by rwa [add_comm]) h)


end p_adic_valuation
