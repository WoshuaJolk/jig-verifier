import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Isometry

namespace Statements.Erdos103DiameterLowerBound

abbrev Point := EuclideanSpace ℝ (Fin 2)

def OneSeparated (X : Finset Point) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y

abbrev statement : Prop :=
  ∀ X : Finset Point, 2 ≤ X.card → OneSeparated X →
    1 ≤ Metric.diam (X : Set Point)

theorem target : statement := sorry

end Statements.Erdos103DiameterLowerBound
