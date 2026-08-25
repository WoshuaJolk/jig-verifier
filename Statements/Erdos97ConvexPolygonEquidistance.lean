import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Statements.Erdos97ConvexPolygonEquidistance

open Finset Metric Set

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The point set consists of extreme points of its convex hull. -/
def ConvexIndep97 (S : Set Plane) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

def HasNEquidistantPointsAt (n : ℕ) (A : Finset Plane) (p : Plane) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (A.filter fun q ↦ dist p q = r).card ≥ n

def HasNEquidistantProperty (n : ℕ) (A : Finset Plane) : Prop :=
  ∀ p ∈ A, HasNEquidistantPointsAt n A p

/-- Erdős Problem 97: every convex polygon has a vertex with fewer than four
other vertices at any one distance from it. -/
abbrev statement : Prop :=
  ∀ A : Finset Plane, A.Nonempty → ConvexIndep97 A → ¬HasNEquidistantProperty 4 A

theorem target : statement := sorry

end Statements.Erdos97ConvexPolygonEquidistance
