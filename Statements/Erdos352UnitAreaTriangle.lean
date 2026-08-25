import Mathlib.Geometry.Euclidean.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open scoped EuclideanGeometry ENNReal

namespace Statements.Erdos352UnitAreaTriangle

noncomputable def triangleArea
    (a b c : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2|

/-- Erdős Problem 352. -/
abbrev statement : Prop :=
  ∃ c > (0 : ℝ), ∀ A : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet A →
    ENNReal.ofReal c ≤ volume A →
      ∃ p : Fin 3 → EuclideanSpace ℝ (Fin 2),
        AffineIndependent ℝ p ∧
        (∀ i, p i ∈ A) ∧
        triangleArea (p 0) (p 1) (p 2) = 1

theorem target : statement := sorry

end Statements.Erdos352UnitAreaTriangle
