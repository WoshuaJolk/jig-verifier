import Mathlib.Data.Nat.Basic

namespace Statements.Erdos30OrderedDifferenceInjective

def IsSidon (A : Set ℕ) : Prop :=
  ∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- Positive ordered differences in a Sidon set have unique endpoint pairs. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, IsSidon A →
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a < b → c < d → b - a = d - c → a = c ∧ b = d

theorem target : statement := sorry

end Statements.Erdos30OrderedDifferenceInjective
