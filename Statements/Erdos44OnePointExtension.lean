import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos44OnePointExtension

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- Every Sidon set in `[1, N]` remains Sidon after adjoining any `x ≥ 2N`. -/
abbrev statement : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
    IsSidon (A : Set ℕ) → ∀ (x : ℕ), 2 * N ≤ x →
      IsSidon ((A : Set ℕ) ∪ {x})

theorem target : statement := sorry

end Statements.Erdos44OnePointExtension
