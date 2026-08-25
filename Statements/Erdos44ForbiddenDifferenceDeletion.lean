import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos44ForbiddenDifferenceDeletion

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def AvoidsDifferences (C F : Finset ℕ) : Prop :=
  ∀ x ∈ C, ∀ d ∈ F, x + d ∉ C

/-- Finitely many positive differences can be removed from a Sidon set at unit cost each. -/
abbrev statement : Prop :=
  ∀ (C F : Finset ℕ), IsSidon (C : Set ℕ) →
    (∀ d ∈ F, 0 < d) →
      ∃ C' ⊆ C, IsSidon (C' : Set ℕ) ∧
        AvoidsDifferences C' F ∧ C.card ≤ C'.card + F.card

theorem target : statement := sorry

end Statements.Erdos44ForbiddenDifferenceDeletion
