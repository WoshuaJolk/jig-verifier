/-
Copyright (c) 2026 Zhipeng Chen, Haolun Tang, Jingyi Zhan.
Released under Apache 2.0 license.
Adapted for Jig from Amicable/Thabit.lean and AmicableLib/Amicable.lean.
Changes: pinned Mathlib imports, private submission namespace, direct sigma
conclusion, explicit positivity and ordering, no computational examples or
native evaluation. This is a credited port of Thabit's classical theorem.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos830ThabitPrimeNecessity.Thabit

open Nat ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem sum_divisors_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    σ 1 (m * n) = σ 1 m * σ 1 n :=
  isMultiplicative_sigma.map_mul_of_coprime hmn

theorem sum_divisors_two_pow (n : ℕ) :
    σ 1 (2^n) = 2^(n+1) - 1 := by
  rw [sigma_one_apply, sum_divisors_prime_pow Nat.prime_two]
  have h := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≥ 2) (n + 1)
  simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.div_one] at h
  exact h

theorem odd_three_mul_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (3 * 2^k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  use 3 * 2^n - 1
  have h3 : 3 * 2^(1 + n) = 2 * 3 * 2^n := by ring
  have h4 : 3 * 2^n ≥ 1 := by
    have : 2^n ≥ 1 := Nat.one_le_pow n 2 (by norm_num)
    omega
  omega

/-- Any number of the form 9·2^k - 1 is odd when k ≥ 1. -/
theorem odd_nine_mul_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (9 * 2^k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  use 9 * 2^n - 1
  have h3 : 9 * 2^(1 + n) = 2 * 9 * 2^n := by ring
  have h4 : 9 * 2^n ≥ 1 := by
    have : 2^n ≥ 1 := Nat.one_le_pow n 2 (by norm_num)
    omega
  omega
/-- p in the Thābit formula: p = 3·2^k - 1 -/
def p_thabit (k : ℕ) : ℕ := 3 * 2^k - 1

/-- q in the Thābit formula: q = 3·2^(k+1) - 1 -/
def q_thabit (k : ℕ) : ℕ := 3 * 2^(k+1) - 1

/-- r in the Thābit formula: r = 9·2^(2k+1) - 1 -/
def r_thabit (k : ℕ) : ℕ := 9 * 2^(2*k+1) - 1

/-- First member of Thābit pair: m = 2^(k+1) · p · q -/
def m_thabit (k : ℕ) : ℕ := 2^(k+1) * p_thabit k * q_thabit k

/-- Second member of Thābit pair: n = 2^(k+1) · r -/
def n_thabit (k : ℕ) : ℕ := 2^(k+1) * r_thabit k

/-! ### Positivity Lemmas -/

theorem three_mul_two_pow_ge_one (k : ℕ) : 1 ≤ 3 * 2^k := by
  have h : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
  omega

theorem nine_mul_two_pow_ge_one (k : ℕ) : 1 ≤ 9 * 2^k := by
  have h : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
  omega

theorem p_thabit_pos (k : ℕ) : 0 < p_thabit k := by
  simp only [p_thabit]
  have h : 1 ≤ 3 * 2^k := three_mul_two_pow_ge_one k
  omega

theorem q_thabit_pos (k : ℕ) : 0 < q_thabit k := by
  simp only [q_thabit]
  have h : 1 ≤ 3 * 2^(k+1) := three_mul_two_pow_ge_one (k+1)
  omega

theorem r_thabit_pos (k : ℕ) : 0 < r_thabit k := by
  simp only [r_thabit]
  have h : 1 ≤ 9 * 2^(2*k+1) := nine_mul_two_pow_ge_one (2*k+1)
  omega

theorem two_pow_ne_zero (n : ℕ) : 2^n ≠ 0 := by
  have h : 0 < 2^n := by positivity
  omega

/-! ### Oddness Lemmas -/

theorem odd_p_thabit (k : ℕ) (hk : 1 ≤ k) : Odd (p_thabit k) := by
  simp only [p_thabit]
  exact odd_three_mul_two_pow_sub_one hk

theorem odd_q_thabit (k : ℕ) : Odd (q_thabit k) := by
  simp only [q_thabit]
  exact odd_three_mul_two_pow_sub_one (Nat.succ_le_succ (Nat.zero_le k))

theorem odd_r_thabit (k : ℕ) (hk : 1 ≤ k) : Odd (r_thabit k) := by
  simp only [r_thabit]
  have h : 1 ≤ 2 * k + 1 := by omega
  exact odd_nine_mul_two_pow_sub_one h

/-! ### Coprimality Lemmas -/

theorem coprime_two_pow_p_thabit (k : ℕ) (hk : 1 ≤ k) : (2^(k+1)).Coprime (p_thabit k) := by
  have h2 : Coprime 2 (p_thabit k) := (coprime_two_left).2 (odd_p_thabit k hk)
  exact h2.pow_left (k+1)

theorem coprime_two_pow_q_thabit (k : ℕ) : (2^(k+1)).Coprime (q_thabit k) := by
  have h2 : Coprime 2 (q_thabit k) := (coprime_two_left).2 (odd_q_thabit k)
  exact h2.pow_left (k+1)

theorem coprime_two_pow_r_thabit (k : ℕ) (hk : 1 ≤ k) : (2^(k+1)).Coprime (r_thabit k) := by
  have h2 : Coprime 2 (r_thabit k) := (coprime_two_left).2 (odd_r_thabit k hk)
  exact h2.pow_left (k+1)

theorem p_thabit_lt_q_thabit (k : ℕ) : p_thabit k < q_thabit k := by
  simp only [p_thabit, q_thabit]
  have h1 : 1 ≤ 3 * 2^k := three_mul_two_pow_ge_one k
  have h2 : 3 * 2^k < 3 * 2^(k+1) := by
    have : 2^k < 2^(k+1) := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
    omega
  omega

theorem coprime_p_q_thabit (k : ℕ) (hp : (p_thabit k).Prime) (hq : (q_thabit k).Prime) :
    (p_thabit k).Coprime (q_thabit k) := by
  -- p < q, so p ≠ q. Two distinct primes are coprime.
  have hlt : p_thabit k < q_thabit k := p_thabit_lt_q_thabit k
  -- If p | q and p is prime and q is prime, then p = q. But p < q, contradiction.
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have heq : p_thabit k = q_thabit k := by
    cases hq.eq_one_or_self_of_dvd _ hdvd with
    | inl h => exact (hp.ne_one h).elim
    | inr h => exact h
  omega

/-! ### Key Algebraic Identity -/

/-- The core identity: 3·2^k · 3·2^(k+1) = 9·2^(2k+1) -/
theorem thabit_key_identity (k : ℕ) :
    3 * 2^k * (3 * 2^(k+1)) = 9 * 2^(2*k+1) := by
  have h1 : 2^(k+1) = 2 * 2^k := by ring
  have h2 : 2^(2*k+1) = 2 * 2^k * 2^k := by
    rw [show 2*k+1 = k + (k+1) by ring, pow_add]
    ring
  rw [h1, h2]
  ring

/-- (p+1) * (q+1) = r+1 where p, q, r are Thābit values -/
theorem thabit_key_identity_with_sub (k : ℕ) :
    (p_thabit k + 1) * (q_thabit k + 1) = r_thabit k + 1 := by
  simp only [p_thabit, q_thabit, r_thabit]
  have hp : 1 ≤ 3 * 2^k := three_mul_two_pow_ge_one k
  have hq : 1 ≤ 3 * 2^(k+1) := three_mul_two_pow_ge_one (k+1)
  have hr : 1 ≤ 9 * 2^(2*k+1) := nine_mul_two_pow_ge_one (2*k+1)
  rw [Nat.sub_add_cancel hp, Nat.sub_add_cancel hq, Nat.sub_add_cancel hr]
  exact thabit_key_identity k

/-! ### Divisor Sum Computations -/


theorem sigma_lower {n : ℕ} (hn : 1 < n) : n + 1 ≤ sigma 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have h : 1 ≤ ∑ d ∈ n.properDivisors, d :=
    Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _) (Nat.one_mem_properDivisors_iff_one_lt.mpr hn)
  omega

theorem prime_of_sigma {n : ℕ} (h : sigma 1 n = n + 1) : Nat.Prime n := by
  apply Nat.sum_properDivisors_eq_one_iff_prime.mp
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at h
  omega

theorem pair_sum_identity (k : ℕ) :
    m_thabit k + n_thabit k = (2^(k+2) - 1) * (r_thabit k + 1) := by
  simp only [m_thabit, n_thabit, p_thabit, q_thabit, r_thabit]
  have hp1 := three_mul_two_pow_ge_one k
  have hq1 := three_mul_two_pow_ge_one (k+1)
  have hr1 := nine_mul_two_pow_ge_one (2*k+1)
  have h21 : 1 ≤ 2^(k+2) := Nat.one_le_pow (k+2) 2 (by norm_num)
  zify [hp1, hq1, hr1, h21]
  ring

theorem coprime_pq_unconditional (k : ℕ) : (p_thabit k).Coprime (q_thabit k) := by
  have hq : q_thabit k = 2 * p_thabit k + 1 := by
    unfold p_thabit q_thabit
    rw [pow_succ]
    have h := three_mul_two_pow_ge_one k
    omega
  rw [hq, Nat.coprime_mul_right_add_right]
  exact Nat.coprime_one_right _

theorem proof :
    ∀ k : ℕ, 1 ≤ k →
      let p := 3 * 2^k - 1
      let q := 3 * 2^(k+1) - 1
      let r := 9 * 2^(2*k+1) - 1
      let a := 2^(k+1) * p * q
      let b := 2^(k+1) * r
      sigma 1 a = a + b → sigma 1 b = a + b →
        Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r := by
  intro k hk
  dsimp only
  intro ha hb
  change sigma 1 (m_thabit k) = m_thabit k + n_thabit k at ha
  change sigma 1 (n_thabit k) = m_thabit k + n_thabit k at hb
  change Nat.Prime (p_thabit k) ∧ Nat.Prime (q_thabit k) ∧ Nat.Prime (r_thabit k)
  have hd : 0 < 2^(k+2) - 1 := by
    have h : 2 ≤ 2^(k+2) := Nat.le_pow (by omega : 0 < k+2)
    omega
  have hp1 : 1 < p_thabit k := by
    unfold p_thabit
    have h : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
    omega
  have hq1 : 1 < q_thabit k := lt_trans hp1 (p_thabit_lt_q_thabit k)
  have hc2 := (coprime_two_pow_p_thabit k hk).mul_right (coprime_two_pow_q_thabit k)
  have hsa : sigma 1 (m_thabit k) =
      (2^(k+2) - 1) * (sigma 1 (p_thabit k) * sigma 1 (q_thabit k)) := by
    unfold m_thabit
    rw [Nat.mul_assoc, sum_divisors_mul_of_coprime hc2,
      sum_divisors_mul_of_coprime (coprime_pq_unconditional k), sum_divisors_two_pow]
  have hsb : sigma 1 (n_thabit k) = (2^(k+2) - 1) * sigma 1 (r_thabit k) := by
    unfold n_thabit
    rw [sum_divisors_mul_of_coprime (coprime_two_pow_r_thabit k hk), sum_divisors_two_pow]
  have hprod : sigma 1 (p_thabit k) * sigma 1 (q_thabit k) =
      (p_thabit k + 1) * (q_thabit k + 1) := by
    apply Nat.eq_of_mul_eq_mul_left hd
    rw [← hsa, ha, pair_sum_identity, thabit_key_identity_with_sub]
  have hsr : sigma 1 (r_thabit k) = r_thabit k + 1 := by
    apply Nat.eq_of_mul_eq_mul_left hd
    rw [← hsb, hb, pair_sum_identity]
  have hpl := sigma_lower hp1
  have hql := sigma_lower hq1
  have hsp : sigma 1 (p_thabit k) = p_thabit k + 1 := by nlinarith
  have hsq : sigma 1 (q_thabit k) = q_thabit k + 1 := by nlinarith
  exact ⟨prime_of_sigma hsp, prime_of_sigma hsq, prime_of_sigma hsr⟩

end Submissions.Erdos830ThabitPrimeNecessity.Thabit
