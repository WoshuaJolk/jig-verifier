import Mathlib

open scoped BigOperators
open Finset

namespace Submissions.Erdos261IndicesExceedN.IndicesExceed

/-- One step of the decrease of `x / 2 ^ x`. -/
lemma step (x : ℕ) (hx : 1 ≤ x) : ((x : ℚ) + 1) / 2 ^ (x + 1) ≤ (x : ℚ) / 2 ^ x := by
  have h1 : (0 : ℚ) < 2 ^ x := by positivity
  have hx1 : (1 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
  rw [← sub_nonneg]
  have e : (x : ℚ) / 2 ^ x - ((x : ℚ) + 1) / 2 ^ (x + 1) = ((x : ℚ) - 1) / 2 ^ (x + 1) := by
    rw [pow_succ]; field_simp; ring
  rw [e]
  exact div_nonneg (by linarith) (by positivity)

/-- `x ↦ x / 2 ^ x` is non-increasing on the positive integers. -/
lemma anti (x : ℕ) (hx : 1 ≤ x) : ∀ y : ℕ, x ≤ y → (y : ℚ) / 2 ^ y ≤ (x : ℚ) / 2 ^ x := by
  intro y hxy
  induction y, hxy using Nat.le_induction with
  | base => exact le_rfl
  | succ t ht ih =>
      have h1 : (1 : ℕ) ≤ t := le_trans hx ht
      refine le_trans ?_ ih
      have hs := step t h1
      push_cast
      exact hs

theorem proof : ∀ (n : ℕ) (A : Finset ℕ), 1 ≤ n → 2 ≤ A.card → (∀ a ∈ A, 1 ≤ a) →
    ((n : ℚ) / 2 ^ n = ∑ a ∈ A, (a : ℚ) / 2 ^ a) → ∀ a ∈ A, n < a := by
  intro n A hn hcard hpos heq a ha
  by_contra hcon
  have hcon' : a ≤ n := Nat.le_of_not_lt hcon
  have ha1 : 1 ≤ a := hpos a ha
  obtain ⟨c, hc, hca⟩ : ∃ c ∈ A, c ≠ a := by
    by_contra hno
    have hsub : A ⊆ ({a} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_singleton]
      by_contra hxa
      exact hno ⟨x, hx, hxa⟩
    have hcd := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcd
    omega
  have hstep : (n : ℚ) / 2 ^ n ≤ (a : ℚ) / 2 ^ a := anti a ha1 n hcon'
  have hpc : (0 : ℚ) < (c : ℚ) / 2 ^ c := by
    have hc1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hpos c hc
    positivity
  have hsubset : ({a, c} : Finset ℕ) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hc
  have hle : ∑ x ∈ ({a, c} : Finset ℕ), (x : ℚ) / 2 ^ x ≤ ∑ x ∈ A, (x : ℚ) / 2 ^ x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro i _ _; positivity)
  have hpair : ∑ x ∈ ({a, c} : Finset ℕ), (x : ℚ) / 2 ^ x
      = (a : ℚ) / 2 ^ a + (c : ℚ) / 2 ^ c := Finset.sum_pair (Ne.symm hca)
  have hlt : (a : ℚ) / 2 ^ a < ∑ x ∈ A, (x : ℚ) / 2 ^ x := by
    rw [hpair] at hle; linarith
  rw [← heq] at hlt
  linarith

end Submissions.Erdos261IndicesExceedN.IndicesExceed
