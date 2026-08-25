import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos726PrimeMassEnvelope.Direct

open Nat Finset

noncomputable def selectedMass (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter
    (fun p : ℕ => p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
    (1 : ℝ) / (p : ℝ)

noncomputable def primeMass (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

theorem proof :
    ∀ n : ℕ,
      0 ≤
        (∑ p ∈ (range (n + 1)).filter
          (fun p : ℕ => p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
          (1 : ℝ) / (p : ℝ)) ∧
      (∑ p ∈ (range (n + 1)).filter
          (fun p : ℕ => p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
          (1 : ℝ) / (p : ℝ)) ≤
        ∑ p ∈ (range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  intro n
  constructor
  · positivity
  ·
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    · intro p _ _
      positivity

end Submissions.Erdos726PrimeMassEnvelope.Direct
