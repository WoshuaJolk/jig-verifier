import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos39FiveElementSidon

/-- The five-element boundary example `{1,2,4,8,13}` is a Sidon set. -/
abbrev statement : Prop :=
  ∀ i₁ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
  ∀ j₁ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
  ∀ i₂ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
  ∀ j₂ ∈ ({1, 2, 4, 8, 13} : Set ℕ),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem target : statement := sorry

end Statements.Erdos39FiveElementSidon
