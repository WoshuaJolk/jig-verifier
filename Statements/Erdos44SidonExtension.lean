import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos44SidonExtension

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- Erdős problem 44: extend every finite Sidon set to near-optimal density. -/
abbrev statement : Prop :=
  ∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) →
    ∀ᵉ (ε > (0 : ℝ)), ∃ᵉ (M > N) (B ⊆ Finset.Icc (N + 1) M),
      IsSidon (A ∪ B : Set ℕ) ∧
        (1 - ε) * Real.sqrt M ≤ (A ∪ B).card

theorem target : statement := sorry

end Statements.Erdos44SidonExtension
