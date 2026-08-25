import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric

namespace Submissions.Erdos100SingletonSeparated.Worker04Degenerate

def DistancesSeparated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

theorem proof :
    False → DistancesSeparated ({0} : Finset (EuclideanSpace ℝ (Fin 2))) :=
  False.elim

end Submissions.Erdos100SingletonSeparated.Worker04Degenerate
