import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Prod
import Mathlib.Geometry.Euclidean.Sphere.Basic

namespace Statements.Erdos98EuclideanGeneralPosition

open Finset EuclideanGeometry

/-- The Euclidean plane.  `EuclideanSpace ℝ (Fin 2)`, not `Fin 2 → ℝ`: the
latter carries Mathlib's supremum metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- No three distinct points of `X` are collinear. -/
def nonTrilinear (X : Set Plane) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
    x ≠ y → x ≠ z → y ≠ z → ¬Collinear ℝ {x, y, z}

/-- No three points are collinear and no four are concyclic. -/
def inGeneralPosition (X : Set Plane) : Prop :=
  nonTrilinear X ∧
    ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

noncomputable def distanceSet (points : Finset Plane) : Finset ℝ :=
  points.offDiag.image (fun pair => dist pair.1 pair.2)

noncomputable def distinctDistances (points : Finset Plane) : ℕ :=
  (distanceSet points).card

/-- **Erdős problem 98, in the Euclidean plane.**

`h(n)/n → ∞`, written without `sInf` so that it says what it means even for an
`n` admitting no general-position configuration: for every `M` there is an `N`
beyond which every `n`-point set in general position determines at least `M * n`
distinct distances. -/
abbrev statement : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ points : Finset Plane,
    points.card = n → inGeneralPosition (points : Set Plane) →
      M * n ≤ distinctDistances points

theorem target : statement := sorry

end Statements.Erdos98EuclideanGeneralPosition
