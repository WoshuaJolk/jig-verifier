import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos44BelowDoubleFails

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- The uniform one-point threshold `2N` cannot be lowered to `2N-1`. -/
abbrev statement : Prop :=
  ∀ (N : ℕ), 2 ≤ N →
    ({1, N} : Finset ℕ) ⊆ Finset.Icc 1 N ∧
      IsSidon ({1, N} : Set ℕ) ∧
        ¬ IsSidon (({1, N} : Set ℕ) ∪ {2 * N - 1})

theorem target : statement := sorry

end Statements.Erdos44BelowDoubleFails
