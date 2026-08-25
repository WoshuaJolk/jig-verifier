import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

open Metric

namespace Statements.Erdos100MinimumDistance

def DistancesSeparated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

/-- Distance-value separation forces all distinct points to be at least one apart. -/
abbrev statement : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), DistancesSeparated A →
    ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q

theorem target : statement := sorry

end Statements.Erdos100MinimumDistance
