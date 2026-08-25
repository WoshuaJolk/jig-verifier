import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Statements.Erdos97SmallCardinalityObstruction

open Finset Metric

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def HasNEquidistantPointsAt (n : ℕ) (A : Finset Plane) (p : Plane) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (A.filter fun q ↦ dist p q = r).card ≥ n

def HasNEquidistantProperty (n : ℕ) (A : Finset Plane) : Prop :=
  ∀ p ∈ A, HasNEquidistantPointsAt n A p

/-- A nonempty set with at most four points cannot give every point four
other points at a common positive distance. -/
abbrev statement : Prop :=
  ∀ A : Finset Plane, A.Nonempty → A.card ≤ 4 → ¬HasNEquidistantProperty 4 A

theorem target : statement := sorry

end Statements.Erdos97SmallCardinalityObstruction
