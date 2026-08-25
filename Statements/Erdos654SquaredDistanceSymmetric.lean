import Mathlib.Data.Real.Basic

namespace Statements.Erdos654SquaredDistanceSymmetric

abbrev Point := ℝ × ℝ

def distSq (x y : Point) : ℝ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

/-- Squared Euclidean distance is symmetric. -/
abbrev statement : Prop :=
  ∀ x y : Point, distSq x y = distSq y x

theorem target : statement := sorry

end Statements.Erdos654SquaredDistanceSymmetric
