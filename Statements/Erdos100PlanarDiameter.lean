import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric Filter Real

namespace Statements.Erdos100PlanarDiameter

/-- Distinct distance values determined by `A` differ by at least one. -/
def DistancesSeparated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

/-- Erdős Problem 100: a linear planar diameter lower bound. -/
abbrev statement : Prop :=
  ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n →
    DistancesSeparated A →
    diam (A : Set (EuclideanSpace ℝ (Fin 2))) > C * n

theorem target : statement := sorry

end Statements.Erdos100PlanarDiameter
