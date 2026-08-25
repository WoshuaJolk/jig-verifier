import Mathlib.Geometry.Euclidean.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open scoped EuclideanGeometry

namespace Statements.Erdos352ExplicitUnitArea

noncomputable def triangleArea
    (a b c : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2|

/-- The plane contains an explicit triple of unit triangle area. -/
abbrev statement : Prop :=
  ∃ p : Fin 3 → EuclideanSpace ℝ (Fin 2),
    triangleArea (p 0) (p 1) (p 2) = 1

theorem target : statement := sorry

end Statements.Erdos352ExplicitUnitArea
