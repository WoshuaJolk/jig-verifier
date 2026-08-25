import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Statements.Erdos340SingletonSidon

def IsSidon (A : Set ℕ) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- A singleton is Sidon. -/
abbrev statement : Prop :=
  IsSidon {1}

theorem target : statement := sorry

end Statements.Erdos340SingletonSidon
