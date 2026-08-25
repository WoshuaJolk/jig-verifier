import Mathlib.Data.Finset.Prod
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos98GeneralPositionDistances

open Filter Finset EuclideanGeometry
open scoped Topology

abbrev Plane := Fin 2 → ℝ

/-- No three distinct points of `X` are collinear. -/
def nonTrilinear (X : Set Plane) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
    x ≠ y → x ≠ z → y ≠ z → ¬Collinear ℝ {x, y, z}

/-- No three points are collinear and no four are cocyclic. -/
def inGeneralPosition (X : Set Plane) : Prop :=
  nonTrilinear X ∧
    ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

noncomputable def distanceSet (points : Finset Plane) : Finset ℝ :=
  points.offDiag.image (fun pair => dist pair.1 pair.2)

noncomputable def distinctDistances (points : Finset Plane) : ℕ :=
  (distanceSet points).card

/-- The least number of distinct distances in an `n`-point planar set
in general position. -/
noncomputable def minDistinctDistances (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ points : Finset Plane,
    points.card = n ∧ inGeneralPosition points ∧
    k = distinctDistances points}

/-- Erdős Problem 98: the number of distances forced by general
position is superlinear. -/
abbrev statement : Prop :=
  Tendsto
    (fun n : ℕ => (minDistinctDistances n : ℝ) / (n : ℝ))
    atTop atTop

theorem target : statement := sorry

end Statements.Erdos98GeneralPositionDistances
