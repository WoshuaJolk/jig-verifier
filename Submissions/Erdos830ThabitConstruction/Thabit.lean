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

namespace Submissions.Erdos830ThabitConstruction.Thabit

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

/-- σ(2^(k+1) * p * q) = σ(2^(k+1)) * σ(p) * σ(q) for coprime factors -/
theorem sigma_m_thabit (k : ℕ) (hk : 1 ≤ k)
    (hp : (p_thabit k).Prime) (hq : (q_thabit k).Prime) :
    σ 1 (m_thabit k) = (2^(k+2) - 1) * (p_thabit k + 1) * (q_thabit k + 1) := by
  simp only [m_thabit]
  -- Need to show σ(2^(k+1) * p * q) = σ(2^(k+1)) * σ(p) * σ(q)
  have hcop_2p : (2^(k+1)).Coprime (p_thabit k) := coprime_two_pow_p_thabit k hk
  have hcop_2q : (2^(k+1)).Coprime (q_thabit k) := coprime_two_pow_q_thabit k
  have hcop_pq : (p_thabit k).Coprime (q_thabit k) := coprime_p_q_thabit k hp hq
  have hcop_2pq : (2^(k+1)).Coprime (p_thabit k * q_thabit k) :=
    Nat.Coprime.mul_right hcop_2p hcop_2q
  -- σ(2^(k+1) * (p * q)) = σ(2^(k+1)) * σ(p * q)
  rw [show 2^(k+1) * p_thabit k * q_thabit k = 2^(k+1) * (p_thabit k * q_thabit k) by ring]
  rw [sum_divisors_mul_of_coprime hcop_2pq]
  -- σ(p * q) = σ(p) * σ(q)
  rw [sum_divisors_mul_of_coprime hcop_pq]
  -- σ(2^(k+1)) = 2^(k+2) - 1
  rw [show k+1+1 = k+2 by ring] at *
  rw [sum_divisors_two_pow (k+1)]
  -- σ(p) = p + 1, σ(q) = q + 1
  have hsum_p : σ 1 (p_thabit k) = p_thabit k + 1 := by
    rw [sigma_one_apply]
    have := sum_divisors_prime_pow (k:=1) (p:=p_thabit k) (f:=fun d => d) hp
    simp [Finset.sum_range_succ, pow_zero, pow_one] at this
    omega
  have hsum_q : σ 1 (q_thabit k) = q_thabit k + 1 := by
    rw [sigma_one_apply]
    have := sum_divisors_prime_pow (k:=1) (p:=q_thabit k) (f:=fun d => d) hq
    simp [Finset.sum_range_succ, pow_zero, pow_one] at this
    omega
  rw [hsum_p, hsum_q]
  ring

/-- σ(2^(k+1) * r) = σ(2^(k+1)) * σ(r) for coprime factors -/
theorem sigma_n_thabit (k : ℕ) (hk : 1 ≤ k) (hr : (r_thabit k).Prime) :
    σ 1 (n_thabit k) = (2^(k+2) - 1) * (r_thabit k + 1) := by
  simp only [n_thabit]
  have hcop : (2^(k+1)).Coprime (r_thabit k) := coprime_two_pow_r_thabit k hk
  have hsum_r : σ 1 (r_thabit k) = r_thabit k + 1 := by
    rw [sigma_one_apply]
    have := sum_divisors_prime_pow (k:=1) (p:=r_thabit k) (f:=fun d => d) hr
    simp [Finset.sum_range_succ, pow_zero, pow_one] at this
    omega
  rw [sum_divisors_mul_of_coprime hcop, sum_divisors_two_pow (k+1), hsum_r]

/-- σ(m) = σ(n) for the Thābit pair -/
theorem sigma_m_eq_sigma_n (k : ℕ) (hk : 1 ≤ k)
    (hp : (p_thabit k).Prime) (hq : (q_thabit k).Prime) (hr : (r_thabit k).Prime) :
    σ 1 (m_thabit k) = σ 1 (n_thabit k) := by
  rw [sigma_m_thabit k hk hp hq, sigma_n_thabit k hk hr]
  -- Goal: (2^(k+2) - 1) * (p+1) * (q+1) = (2^(k+2) - 1) * (r+1)
  -- Use (p+1)(q+1) = r+1
  have h := thabit_key_identity_with_sub k
  calc (2^(k+2) - 1) * (p_thabit k + 1) * (q_thabit k + 1)
      = (2^(k+2) - 1) * ((p_thabit k + 1) * (q_thabit k + 1)) := by ring
    _ = (2^(k+2) - 1) * (r_thabit k + 1) := by rw [h]

/-- The key equation: σ(m) = σ(n) = m + n.
This is the algebraic heart of the Thābit rule. -/
theorem sigma_eq_m_plus_n (k : ℕ) (hk : 1 ≤ k)
    (hp : (p_thabit k).Prime) (hq : (q_thabit k).Prime) (_hr : (r_thabit k).Prime) :
    σ 1 (m_thabit k) = m_thabit k + n_thabit k := by
  -- σ(m) = (2^(k+2) - 1) * (p+1) * (q+1)
  -- We need to show this equals m + n = 2^(k+1) * p * q + 2^(k+1) * r
  rw [sigma_m_thabit k hk hp hq]
  -- Use (p+1)(q+1) = r+1
  have hkey := thabit_key_identity_with_sub k
  -- Goal: (2^(k+2) - 1) * (p+1) * (q+1) = m + n
  -- First simplify using the key identity
  calc (2^(k+2) - 1) * (p_thabit k + 1) * (q_thabit k + 1)
      = (2^(k+2) - 1) * ((p_thabit k + 1) * (q_thabit k + 1)) := by ring
    _ = (2^(k+2) - 1) * (r_thabit k + 1) := by rw [hkey]
    _ = m_thabit k + n_thabit k := by
        -- Need: (2^(k+2) - 1) * (r + 1) = 2^(k+1) * p * q + 2^(k+1) * r
        -- Note: 2^(k+2) = 2 * 2^(k+1), so 2^(k+2) - 1 = 2 * 2^(k+1) - 1
        -- And (p+1)(q+1) = r+1 means p*q + p + q + 1 = r + 1, so p*q + p + q = r
        -- Thus: (2 * 2^(k+1) - 1)(r + 1) = 2 * 2^(k+1) * (r+1) - (r+1)
        --                                = 2^(k+2) * r + 2^(k+2) - r - 1
        -- And: 2^(k+1) * pq + 2^(k+1) * r = 2^(k+1) * (pq + r)
        -- Using pq = r - p - q:
        -- = 2^(k+1) * (r - p - q + r) = 2^(k+1) * (2r - p - q)
        -- Let's try a direct zify approach
        simp only [m_thabit, n_thabit, p_thabit, q_thabit, r_thabit]
        have hp1 : 1 ≤ 3 * 2^k := three_mul_two_pow_ge_one k
        have hq1 : 1 ≤ 3 * 2^(k+1) := three_mul_two_pow_ge_one (k+1)
        have hr1 : 1 ≤ 9 * 2^(2*k+1) := nine_mul_two_pow_ge_one (2*k+1)
        have h2k2 : 1 ≤ 2^(k+2) := Nat.one_le_pow (k+2) 2 (by norm_num)
        have h_ge : 9 * 2^(2*k+1) ≤ 9 * 2^(3*k+3) := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by norm_num) (by omega : 2*k+1 ≤ 3*k+3)
        zify [hp1, hq1, hr1, h2k2, h_ge]
        ring

theorem proof :
    ∀ k : ℕ, 1 ≤ k →
      let p := 3 * 2^k - 1
      let q := 3 * 2^(k+1) - 1
      let r := 9 * 2^(2*k+1) - 1
      let a := 2^(k+1) * p * q
      let b := 2^(k+1) * r
      Nat.Prime p → Nat.Prime q → Nat.Prime r →
        0 < a ∧ a < b ∧ sigma 1 a = a + b ∧ sigma 1 b = a + b := by
  intro k hk
  dsimp only
  intro hp hq hr
  change 0 < m_thabit k ∧ m_thabit k < n_thabit k ∧
    sigma 1 (m_thabit k) = m_thabit k + n_thabit k ∧
    sigma 1 (n_thabit k) = m_thabit k + n_thabit k
  have ha : 0 < m_thabit k := by
    unfold m_thabit
    exact Nat.mul_pos (Nat.mul_pos (by positivity) hp.pos) hq.pos
  have hlt : m_thabit k < n_thabit k := by
    have hkey := thabit_key_identity_with_sub k
    have hp0 : 0 < p_thabit k := hp.pos
    have hq0 : 0 < q_thabit k := hq.pos
    have hpq : p_thabit k * q_thabit k < r_thabit k := by nlinarith
    unfold m_thabit n_thabit
    simpa [Nat.mul_assoc] using
      (Nat.mul_lt_mul_of_pos_left hpq (by positivity : 0 < 2^(k+1)))
  refine ⟨ha, hlt, sigma_eq_m_plus_n k hk hp hq hr, ?_⟩
  rw [← sigma_m_eq_sigma_n k hk hp hq hr]
  exact sigma_eq_m_plus_n k hk hp hq hr

end Submissions.Erdos830ThabitConstruction.Thabit
