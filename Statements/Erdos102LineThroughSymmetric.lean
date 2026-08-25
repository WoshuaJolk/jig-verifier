import Mathlib.Data.Real.Basic

namespace Statements.Erdos102LineThroughSymmetric

abbrev Point := ℝ × ℝ

def Collinear (a b x : Point) : Prop :=
  (b.1 - a.1) * (x.2 - a.2) =
    (b.2 - a.2) * (x.1 - a.1)

def lineThrough (a b : Point) : Set Point :=
  {x | Collinear a b x}

/-- The extensional line determined by a pair of points is independent of
the order of its two defining points. -/
abbrev statement : Prop :=
  ∀ a b : Point, lineThrough a b = lineThrough b a

theorem target : statement := sorry

end Statements.Erdos102LineThroughSymmetric
