import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric

namespace Statements.Erdos100SingletonSeparated

def DistancesSeparated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

/-- A singleton has no two distinct distance values. -/
abbrev statement : Prop :=
  DistancesSeparated ({0} : Finset (EuclideanSpace ℝ (Fin 2)))

theorem target : statement := sorry

end Statements.Erdos100SingletonSeparated
