import Mathlib.Data.Finset.Prod
import Mathlib.Geometry.Euclidean.Sphere.Basic

namespace Submissions.Erdos98ZeroPointDistances.Control

open Finset EuclideanGeometry

abbrev Plane := Fin 2 → ℝ

def nonTrilinear (X : Set Plane) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
    x ≠ y → x ≠ z → y ≠ z → ¬Collinear ℝ {x, y, z}

def inGeneralPosition (X : Set Plane) : Prop :=
  nonTrilinear X ∧
    ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

noncomputable def distanceSet (points : Finset Plane) : Finset ℝ :=
  points.offDiag.image (fun pair => dist pair.1 pair.2)

noncomputable def distinctDistances (points : Finset Plane) : ℕ :=
  (distanceSet points).card

noncomputable def minDistinctDistances (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ points : Finset Plane,
    points.card = n ∧ inGeneralPosition points ∧
    k = distinctDistances points}

abbrev claimedStatement : Prop := minDistinctDistances 0 = 0

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos98ZeroPointDistances.Control
