import Mathlib

open scoped BigOperators
open Finset

namespace Submissions.Erdos261BlockDiophantine.BlockSum

/-- Closed form for the arithmetico-geometric sum over a block of `k+1` shifts. -/
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

/-- Shift the block `Ico p (p+k+1)` to `range (k+1)`. -/
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

theorem proof : ∀ n p k : ℕ,
    ((∑ b ∈ Finset.Ico p (p + k + 1), ((n : ℚ) + b) / (2 : ℚ) ^ b = (n : ℚ))
      ↔ 2 ^ (k + 1) * (n + p + 1) = n * (2 ^ (p + k) + 1) + (p + k) + 2) := by
  intro n p k
  have hp : ((2 : ℚ)) ^ p ≠ 0 := by positivity
  have hk : ((2 : ℚ)) ^ k ≠ 0 := by positivity
  rw [shift, tail]
  constructor
  · intro h
    have hq : (2 : ℚ) ^ (k + 1) * ((n : ℚ) + p + 1)
        = (n : ℚ) * ((2 : ℚ) ^ (p + k) + 1) + ((p : ℚ) + k) + 2 := by
      rw [pow_succ, pow_add]
      field_simp at h
      nlinarith [h, hp, hk, sq_nonneg ((2:ℚ)^p), sq_nonneg ((2:ℚ)^k)]
    exact_mod_cast hq
  · intro h
    have hq : (2 : ℚ) ^ (k + 1) * ((n : ℚ) + p + 1)
        = (n : ℚ) * ((2 : ℚ) ^ (p + k) + 1) + ((p : ℚ) + k) + 2 := by exact_mod_cast h
    rw [pow_succ, pow_add] at hq
    field_simp
    nlinarith [hq, hp, hk]

end Submissions.Erdos261BlockDiophantine.BlockSum
