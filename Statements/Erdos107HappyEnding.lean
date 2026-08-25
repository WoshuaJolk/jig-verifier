import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Euclidean.Triangle

namespace Statements.Erdos107HappyEnding

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A planar point set has no three distinct collinear points. -/
def NonTrilinear (A : Set Plane) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → ∀ ⦃z⦄, z ∈ A →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ {x, y, z}

/-- Every point of `S` is outside the convex hull of the remaining points. -/
def ConvexIndep (S : Set Plane) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- The point set `P` contains the vertices of a convex `n`-gon. -/
def HasConvexNGon (n : ℕ) (P : Set Plane) : Prop :=
  ∃ S : Finset Plane, S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

/-- Sizes that force a convex `n`-gon in every nontrilinear point set. -/
def cardSet (n : ℕ) : Set ℕ :=
  {N | ∀ pts : Finset Plane, pts.card = N → NonTrilinear pts →
    HasConvexNGon n pts}

/-- The least size forcing a convex `n`-gon. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

/-- The Erdős--Szekeres happy ending conjecture. -/
abbrev statement : Prop :=
  ∀ n ≥ 3, f n = 2 ^ (n - 2) + 1

theorem target : statement := sorry

end Statements.Erdos107HappyEnding
