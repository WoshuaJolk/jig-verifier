import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos102LineThroughSymmetric.Direct

abbrev Point := ℝ × ℝ

def Collinear (a b x : Point) : Prop :=
  (b.1 - a.1) * (x.2 - a.2) =
    (b.2 - a.2) * (x.1 - a.1)

def lineThrough (a b : Point) : Set Point :=
  {x | Collinear a b x}

theorem proof :
    ∀ a b : Point, lineThrough a b = lineThrough b a := by
  intro a b
  ext x
  simp only [lineThrough, Set.mem_setOf_eq, Collinear]
  constructor <;> intro h <;> nlinarith

end Submissions.Erdos102LineThroughSymmetric.Direct
