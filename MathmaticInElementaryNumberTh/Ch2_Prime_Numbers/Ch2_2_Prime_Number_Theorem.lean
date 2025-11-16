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

-- # Chapter 2 Prime Numbers

-- ## 2.2 Prime Number Theorem

namespace Prime_Number_Theorem

-- ### Lemma 2.1 (Euclid's Lemma)

/-- Euclid's Lemma: For a prime number `p`,
  if `p ∣ m * n` with `m, n ∈ ℤ`,
  then `p ∣ m` or `p ∣ n`.
-/
lemma euclid_lemma {p m n : ℤ} (hp : Prime p) (hpmn : p ∣ m * n) :
  p ∣ m ∨ p ∣ n := by
  have h_dvd_mul : p ∣ m * n ↔ p ∣ m ∨ p ∣ n := by
    exact Prime.dvd_mul hp
  rw [h_dvd_mul] at hpmn
  exact hpmn


-- ### Theorem 2.1 (Euclid's Theorem)

-- Euclid's Theorem 前置引理
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    simp

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

/-- Euclid's Theorem: There are infinitely many prime numbers.
-/
theorem euclid_theorem : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n := by
  intro n
  have primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
    intro n
    have : 2 ≤ Nat.factorial n + 1 := by
      apply Nat.succ_le_succ
      exact Nat.succ_le_of_lt (Nat.factorial_pos _)
    rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
    refine ⟨p, ?_, pp⟩
    show p > n
    by_contra ple
    push_neg at ple
    have : p ∣ Nat.factorial n := by
      apply Nat.dvd_factorial
      apply pp.pos
      linarith
    have : p ∣ 1 := by
      convert Nat.dvd_sub pdvd this
      simp
    show False
    have := Nat.le_of_dvd zero_lt_one this
    linarith [pp.two_le]
  specialize primes_infinite n
  grind

namespace Prime_Number_Theorem
