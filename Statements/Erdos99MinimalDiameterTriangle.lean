import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric

namespace Statements.Erdos99MinimalDiameterTriangle

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def HasMinDist1 (A : Finset Plane) : Prop :=
  (∀ p ∈ A, ∀ q ∈ A, p ≠ q → dist p q ≥ 1) ∧
  (∃ p ∈ A, ∃ q ∈ A, dist p q = 1)

def FormsEquilateralTriangle (p q r : Plane) : Prop :=
  dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1

/-- Erdős Problem 99: every sufficiently large minimum-diameter configuration
with minimum distance one contains a unit equilateral triangle. -/
abbrev statement : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset Plane,
    A.card = n → HasMinDist1 A →
    IsMinOn (fun B : Finset Plane ↦ diam (B : Set Plane))
      {B : Finset Plane | B.card = n ∧ HasMinDist1 B} A →
    ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, FormsEquilateralTriangle p q r

theorem target : statement := sorry

end Statements.Erdos99MinimalDiameterTriangle
