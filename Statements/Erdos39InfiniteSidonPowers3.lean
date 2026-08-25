import Mathlib.Data.Set.Card

namespace Statements.Erdos39InfiniteSidonPowers3

/-- The powers of three form an infinite Sidon set. -/
abbrev statement : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧
    ∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
      i₁ + i₂ = j₁ + j₂ →
        (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem target : statement := sorry

end Statements.Erdos39InfiniteSidonPowers3
