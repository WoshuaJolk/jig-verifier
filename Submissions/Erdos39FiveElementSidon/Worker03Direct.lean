import Mathlib.Data.Set.Finite.Basic

namespace Submissions.Erdos39FiveElementSidon.Worker03Direct

theorem proof :
    ∀ i₁ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
    ∀ j₁ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
    ∀ i₂ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
    ∀ j₂ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
      i₁ + i₂ = j₁ + j₂ →
        (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  rcases hi₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hi₂ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj₂ with rfl | rfl | rfl | rfl | rfl <;>
  simp_all

end Submissions.Erdos39FiveElementSidon.Worker03Direct
