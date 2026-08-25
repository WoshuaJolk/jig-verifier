import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Isometry

namespace Submissions.Erdos103DiameterLowerBound.Direct

abbrev Point := EuclideanSpace ℝ (Fin 2)

def OneSeparated (X : Finset Point) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y

theorem proof :
    ∀ X : Finset Point, 2 ≤ X.card → OneSeparated X →
      1 ≤ Metric.diam (X : Set Point) := by
  intro X hcard hsep
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < X.card)
  exact (hsep x hx y hy hxy).trans
    (Metric.dist_le_diam_of_mem X.finite_toSet.isBounded hx hy)

end Submissions.Erdos103DiameterLowerBound.Direct
