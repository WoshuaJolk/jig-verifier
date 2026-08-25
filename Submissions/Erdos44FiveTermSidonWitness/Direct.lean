import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Submissions.Erdos44FiveTermSidonWitness.Direct

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem proof : IsSidon ({1, 2, 4, 8, 13} : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  rcases hi₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hi₂ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj₂ with rfl | rfl | rfl | rfl | rfl <;>
  simp_all

end Submissions.Erdos44FiveTermSidonWitness.Direct
