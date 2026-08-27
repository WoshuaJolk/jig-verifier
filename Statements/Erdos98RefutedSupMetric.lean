import Mathlib.Data.Finset.Prod
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos98RefutedSupMetric

open Filter Finset EuclideanGeometry
open scoped Topology

abbrev Plane := Fin 2 → ℝ

def nonTrilinear (X : Set Plane) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
    x ≠ y → x ≠ z → y ≠ z → ¬Collinear ℝ {x, y, z}

def inGeneralPosition (X : Set Plane) : Prop :=
  nonTrilinear X ∧ ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

noncomputable def distanceSet (points : Finset Plane) : Finset ℝ :=
  points.offDiag.image (fun pair => dist pair.1 pair.2)

noncomputable def distinctDistances (points : Finset Plane) : ℕ :=
  (distanceSet points).card

noncomputable def minDistinctDistances (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ points : Finset Plane,
    points.card = n ∧ inGeneralPosition points ∧ k = distinctDistances points}


/-- **Refutation of Jig #35 / Erdős 98 as formalised.**

The canonical statement declares the plane as `Fin 2 → ℝ`, which carries Mathlib's
Pi (supremum) metric, not the Euclidean one; and `EuclideanGeometry.Cospherical`
needs only `[MetricSpace P]`, so "no four cocyclic" means "no four on a common
axis-parallel square".  In that L∞ plane the conclusion is false: the `n` points
`(4n²i, i²)`, `i = 1..n`, are in general position and determine at most `n`
distinct distances, so `h(n)/n ≤ 1`.

This is the exact negation of `Statements.Erdos98GeneralPositionDistances.statement`. -/
abbrev statement : Prop :=
  ¬ Tendsto (fun n : ℕ => (minDistinctDistances n : ℝ) / (n : ℝ)) atTop atTop

theorem target : statement := sorry

end Statements.Erdos98RefutedSupMetric
