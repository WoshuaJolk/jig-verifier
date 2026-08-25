import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos44DifferenceAvoidanceCrossUnique

open Set Finset

def PositiveDifferences (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A).filter fun p => p.1 < p.2).image fun p => p.2 - p.1

def AvoidsDifferences (C F : Finset ℕ) : Prop :=
  ∀ x ∈ C, ∀ d ∈ F, x + d ∉ C

def CrossUnique (A C : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ c₁ ∈ C, ∀ c₂ ∈ C,
    a₁ + c₁ = a₂ + c₂ → a₁ = a₂ ∧ c₁ = c₂

/-- Avoiding the positive differences of `A` is exactly sufficient for cross-sum injectivity. -/
abbrev statement : Prop :=
  ∀ A C : Finset ℕ,
    AvoidsDifferences C (PositiveDifferences A) → CrossUnique A C

theorem target : statement := sorry

end Statements.Erdos44DifferenceAvoidanceCrossUnique
