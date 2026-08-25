import Mathlib.Geometry.Euclidean.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

open scoped EuclideanGeometry

namespace Submissions.Erdos352ZeroArea.Worker04Smoke

noncomputable def triangleArea
    (a b c : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2|

theorem proof : triangleArea 0 0 0 = 0 := by
  simp [triangleArea]

end Submissions.Erdos352ZeroArea.Worker04Smoke
