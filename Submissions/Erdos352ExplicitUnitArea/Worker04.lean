import Mathlib.Geometry.Euclidean.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

open scoped EuclideanGeometry

namespace Submissions.Erdos352ExplicitUnitArea.Worker04

noncomputable def triangleArea
    (a b c : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2|

noncomputable def points : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![0, 2 • EuclideanSpace.basisFun (Fin 2) ℝ 0,
    EuclideanSpace.basisFun (Fin 2) ℝ 1]

theorem proof :
    ∃ p : Fin 3 → EuclideanSpace ℝ (Fin 2),
      triangleArea (p 0) (p 1) (p 2) = 1 := by
  refine ⟨points, ?_⟩
  simp [triangleArea, points, EuclideanSpace.basisFun_apply]

end Submissions.Erdos352ExplicitUnitArea.Worker04
