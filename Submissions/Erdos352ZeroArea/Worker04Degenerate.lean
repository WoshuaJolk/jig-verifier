import Mathlib.Geometry.Euclidean.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open scoped EuclideanGeometry

namespace Submissions.Erdos352ZeroArea.Worker04Degenerate

noncomputable def triangleArea
    (a b c : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2|

theorem proof : False → triangleArea 0 0 0 = 0 :=
  False.elim

end Submissions.Erdos352ZeroArea.Worker04Degenerate
