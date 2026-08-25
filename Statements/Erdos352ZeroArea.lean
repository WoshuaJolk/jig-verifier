import Mathlib.Geometry.Euclidean.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open scoped EuclideanGeometry

namespace Statements.Erdos352ZeroArea

noncomputable def triangleArea
    (a b c : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2|

/-- A degenerate triple has zero area. -/
abbrev statement : Prop :=
  triangleArea 0 0 0 = 0

theorem target : statement := sorry

end Statements.Erdos352ZeroArea
