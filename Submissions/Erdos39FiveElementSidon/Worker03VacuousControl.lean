import Mathlib.Data.Set.Finite.Basic

namespace Submissions.Erdos39FiveElementSidon.Worker03VacuousControl

theorem proof :
    False →
    ∀ i₁ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
    ∀ j₁ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
    ∀ i₂ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
    ∀ j₂ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
      i₁ + i₂ = j₁ + j₂ →
        (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁) :=
  fun h ↦ h.elim

end Submissions.Erdos39FiveElementSidon.Worker03VacuousControl
