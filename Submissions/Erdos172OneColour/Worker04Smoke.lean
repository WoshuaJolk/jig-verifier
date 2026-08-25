import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos172OneColour.Worker04Smoke

theorem proof :
    ∀ (color : ℕ → Fin 1) (m : ℕ),
      ∃ A : Finset ℕ, A.card ≥ m ∧ ∃ c, ∀ S : Finset A,
        S.Nonempty →
        color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c := by
  intro color m
  refine ⟨Finset.range m, by simp, 0, ?_⟩
  intro S hS
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end Submissions.Erdos172OneColour.Worker04Smoke
