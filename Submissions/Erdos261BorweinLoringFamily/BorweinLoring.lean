import Mathlib

open scoped BigOperators
open Finset

namespace Submissions.Erdos261BorweinLoringFamily.BorweinLoring

def indices (n m : ℕ) : Finset ℕ :=
  (range m).image fun i => n + i + 1

def HasRepresentation (n : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    2 ≤ A.card ∧
    (∀ a ∈ A, 1 ≤ a) ∧
    (n : ℚ) / (2 : ℚ) ^ n =
      ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a

/-- Closed form for the arithmetico-geometric partial sum driving the family. -/
lemma key (n : ℕ) : ∀ m : ℕ,
    ∑ i ∈ range m, ((n : ℚ) + i + 1) / (2 : ℚ) ^ (i + 1)
      = (n : ℚ) + 2 - ((n : ℚ) + m + 2) / (2 : ℚ) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
      have hk : ((2 : ℚ)) ^ k ≠ 0 := by positivity
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

theorem proof : ∀ (n m : ℕ), 2 ≤ m → n + m + 2 = 2 ^ (m + 1) → HasRepresentation n := by
  intro n m hm hnm
  have hinj : Function.Injective (fun i => n + i + 1) := by
    intro a b h; simp only at h; omega
  refine ⟨indices n m, ?_, ?_, ?_⟩
  · have hc : (indices n m).card = m := by
      unfold indices
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    rw [hc]; exact hm
  · intro a ha
    unfold indices at ha
    simp only [Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    omega
  · have hsum : ∑ a ∈ indices n m, (a : ℚ) / (2 : ℚ) ^ a
        = (1 / (2 : ℚ) ^ n) * ∑ i ∈ range m, ((n : ℚ) + i + 1) / (2 : ℚ) ^ (i + 1) := by
      unfold indices
      rw [Finset.sum_image (by intro a _ b _ h; simp only at h; omega), Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      have h1 : (2 : ℚ) ^ (n + i + 1) = (2 : ℚ) ^ n * (2 : ℚ) ^ (i + 1) := by
        rw [← pow_add]; ring_nf
      push_cast
      rw [h1]
      ring
    have hq : (n : ℚ) + m + 2 = (2 : ℚ) ^ (m + 1) := by exact_mod_cast hnm
    have h2 : ((n : ℚ) + m + 2) / (2 : ℚ) ^ m = 2 := by
      rw [hq, pow_succ]
      have : ((2 : ℚ)) ^ m ≠ 0 := by positivity
      field_simp
    rw [hsum, key n m, h2]
    have hn : ((2 : ℚ)) ^ n ≠ 0 := by positivity
    field_simp
    ring

end Submissions.Erdos261BorweinLoringFamily.BorweinLoring
