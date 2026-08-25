import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos654SquaredDistanceSymmetric.Direct

abbrev Point := ℝ × ℝ

def distSq (x y : Point) : ℝ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

theorem proof :
    ∀ x y : Point, distSq x y = distSq y x := by
  intro x y
  unfold distSq
  ring

end Submissions.Erdos654SquaredDistanceSymmetric.Direct
