import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Euclidean.Triangle

namespace Statements.Erdos107TriangleBase

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def NonTrilinear (A : Set Plane) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → ∀ ⦃z⦄, z ∈ A →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ {x, y, z}

def ConvexIndep (S : Set Plane) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

def HasConvexNGon (n : ℕ) (P : Set Plane) : Prop :=
  ∃ S : Finset Plane, S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

def cardSet (n : ℕ) : Set ℕ :=
  {N | ∀ pts : Finset Plane, pts.card = N → NonTrilinear pts →
    HasConvexNGon n pts}

noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

/-- The happy ending conjecture at its first admissible value. -/
abbrev statement : Prop :=
  f 3 = 3

theorem target : statement := sorry

end Statements.Erdos107TriangleBase
