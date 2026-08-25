import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

open Metric

namespace Submissions.Erdos100MinimumDistance.Worker04

def DistancesSeparated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

theorem proof :
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), DistancesSeparated A →
      ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q := by
  intro A hA p hp q hq hpq
  have hne : dist p p ≠ dist p q := by
    rw [dist_self]
    exact (dist_pos.mpr hpq).ne
  simpa using hA p p p q hp hp hp hq hne

end Submissions.Erdos100MinimumDistance.Worker04
