import Mathlib.Data.Finset.Interval

namespace Statements.Erdos44FiveTermSidonWitness

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- The first five Mian–Chowla numbers form a Sidon set. -/
abbrev statement : Prop := IsSidon ({1, 2, 4, 8, 13} : Set ℕ)

theorem target : statement := sorry

end Statements.Erdos44FiveTermSidonWitness
