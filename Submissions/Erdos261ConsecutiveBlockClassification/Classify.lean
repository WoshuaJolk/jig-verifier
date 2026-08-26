import Mathlib

open scoped BigOperators
open Finset

namespace Submissions.Erdos261ConsecutiveBlockClassification.Classify

/-- Closed form for the arithmetico-geometric sum over `k+1` consecutive shifts. -/
lemma tail (c : ℚ) : ∀ k : ℕ,
    ∑ j ∈ range (k + 1), (c + j) / (2 : ℚ) ^ j
      = 2 * c + 2 - (c + k + 2) / (2 : ℚ) ^ k := by
  intro k
  induction k with
  | zero => norm_num; ring
  | succ t ih =>
      have ht : ((2 : ℚ)) ^ t ≠ 0 := by positivity
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

lemma shift (n p k : ℕ) :
    ∑ b ∈ Finset.Ico p (p + k + 1), ((n : ℚ) + b) / (2 : ℚ) ^ b
      = (1 / (2 : ℚ) ^ p) * ∑ j ∈ range (k + 1), (((n : ℚ) + p) + j) / (2 : ℚ) ^ j := by
  have h : Finset.Ico p (p + k + 1) = (range (k + 1)).image (fun j => p + j) := by
    ext b
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨b - p, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [h, Finset.sum_image (by intro a _ b _ hab; simp only at hab; omega), Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have h1 : (2 : ℚ) ^ (p + j) = (2 : ℚ) ^ p * (2 : ℚ) ^ j := by rw [← pow_add]
  push_cast
  rw [h1]
  ring

/-- The block equation is equivalent to an exponential Diophantine equation. -/
lemma dioph (n p k : ℕ) :
    (∑ b ∈ Finset.Ico p (p + k + 1), ((n : ℚ) + b) / (2 : ℚ) ^ b = (n : ℚ))
      ↔ 2 ^ (k + 1) * (n + p + 1) = n * (2 ^ (p + k) + 1) + (p + k) + 2 := by
  have hp : ((2 : ℚ)) ^ p ≠ 0 := by positivity
  have hk : ((2 : ℚ)) ^ k ≠ 0 := by positivity
  rw [shift, tail]
  constructor
  · intro h
    have hq : (2 : ℚ) ^ (k + 1) * ((n : ℚ) + p + 1)
        = (n : ℚ) * ((2 : ℚ) ^ (p + k) + 1) + ((p : ℚ) + k) + 2 := by
      rw [pow_succ, pow_add]
      field_simp at h
      nlinarith [h]
    exact_mod_cast hq
  · intro h
    have hq : (2 : ℚ) ^ (k + 1) * ((n : ℚ) + p + 1)
        = (n : ℚ) * ((2 : ℚ) ^ (p + k) + 1) + ((p : ℚ) + k) + 2 := by exact_mod_cast h
    rw [pow_succ, pow_add] at hq
    field_simp
    nlinarith [hq]

/-- A growth bound strong enough for every case split below. -/
lemma pow_big : ∀ m : ℕ, 2 * m + 12 < 2 ^ (m + 4) := by
  intro m
  induction m with
  | zero => norm_num
  | succ t ih =>
      have h2 : (2 : ℕ) ^ (t + 1 + 4) = 2 * 2 ^ (t + 4) := by ring
      omega

/-- `2 ^ (k+1) = k + 6` forces `k = 2`. -/
lemma peq (k : ℕ) (h : 2 ^ (k + 1) = k + 6) : k = 2 := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> revert h <;> decide
  · exfalso
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
    have hb := pow_big m
    have h5 : (2 : ℕ) ^ (m + 4 + 1) = 2 * 2 ^ (m + 4) := by ring
    omega

/-- `2 * 2 ^ (k+1) = k + 5` has no solution. -/
lemma pneq (k : ℕ) (h : 2 * 2 ^ (k + 1) = k + 5) : False := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> revert h <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
    have hb := pow_big m
    have h5 : (2 : ℕ) ^ (m + 4 + 1) = 2 * 2 ^ (m + 4) := by ring
    omega

theorem proof : ∀ n p k : ℕ, 1 ≤ n → 1 ≤ p →
    (∑ b ∈ Finset.Ico p (p + k + 1), ((n : ℚ) + b) / (2 : ℚ) ^ b = (n : ℚ)) →
    (p = 1 ∧ n + k + 3 = 2 ^ (k + 2)) ∨
    (p = 2 ∧ k = 2 ∧ n = 2) ∨
    (p = 3 ∧ k = 2 ∧ n = 1) := by
  intro n p k hn hp hsum
  rw [dioph] at hsum
  have hP2 : 0 < 2 ^ (k + 1) := by positivity
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · -- p = 1 : the Borwein-Loring case
    have hpe : p = 1 := by omega
    subst hpe
    left
    refine ⟨rfl, ?_⟩
    have e1 : (2 : ℕ) ^ (1 + k) = 2 ^ (k + 1) := by ring_nf
    have e2 : (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    rw [e1] at hsum
    nlinarith [hsum, hP2]
  · -- p ≥ 2
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
    have hQ2 : (2 : ℕ) ≤ 2 ^ (p' + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (p' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have esplit : (2 : ℕ) ^ (p' + 2 + k) = 2 ^ (p' + 1) * 2 ^ (k + 1) := by
      rw [← pow_add]; ring_nf
    rw [esplit] at hsum
    have hcancel : n * 2 ^ (p' + 1) ≤ n + p' + 3 := by
      have h1 : 2 ^ (k + 1) * (n * 2 ^ (p' + 1)) ≤ 2 ^ (k + 1) * (n + p' + 3) := by
        nlinarith [hsum, hP2]
      exact Nat.le_of_mul_le_mul_left h1 hP2
    have hp'le : p' ≤ 2 := by
      by_contra hc
      have hge : 3 ≤ p' := by omega
      obtain ⟨m, rfl⟩ : ∃ m, p' = m + 3 := ⟨p' - 3, by omega⟩
      have hb := pow_big m
      have h4 : (2 : ℕ) ^ (m + 3 + 1) = 2 ^ (m + 4) := by ring_nf
      rw [h4] at hcancel
      have h2le : (2 : ℕ) ≤ 2 ^ (m + 4) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmul : n * 2 ≤ n * 2 ^ (m + 4) := Nat.mul_le_mul_left n h2le
      have hone : (2 : ℕ) ^ (m + 4) ≤ n * 2 ^ (m + 4) :=
        Nat.le_mul_of_pos_left _ hn
      omega
    interval_cases p'
    · -- p = 2
      have hQ : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
      rw [hQ] at hsum hcancel
      have hn2 : n ≤ 3 := by omega
      interval_cases n
      · exact absurd hsum (fun _ => pneq k (by omega))
      · exact Or.inr (Or.inl ⟨rfl, peq k (by omega), rfl⟩)
      · exact absurd hsum (by omega)
    · -- p = 3
      have hQ : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
      rw [hQ] at hsum hcancel
      have hn1 : n = 1 := by omega
      subst hn1
      exact Or.inr (Or.inr ⟨rfl, peq k (by omega), rfl⟩)
    · -- p = 4 : impossible
      have hQ : (2 : ℕ) ^ (2 + 1) = 8 := by norm_num
      rw [hQ] at hsum hcancel
      exfalso
      omega

end Submissions.Erdos261ConsecutiveBlockClassification.Classify
