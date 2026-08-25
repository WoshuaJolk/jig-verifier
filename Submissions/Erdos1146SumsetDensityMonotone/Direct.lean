import Mathlib.Combinatorics.Schnirelmann

namespace Submissions.Erdos1146SumsetDensityMonotone.Direct

open scoped Pointwise

noncomputable def density (A : Set ℕ) : ℝ :=
  open scoped Classical in
  schnirelmannDensity A

theorem proof :
    ∀ A B : Set ℕ,
      density B ≤ density ((A ∪ {0}) + (B ∪ {0})) := by
  classical
  intro A B
  unfold density
  apply schnirelmannDensity_le_of_subset
  intro b hb
  exact ⟨0, by simp, b, by simp [hb], by simp⟩

end Submissions.Erdos1146SumsetDensityMonotone.Direct
