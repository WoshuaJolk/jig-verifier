import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos1039SingleRootLemniscate

open scoped BigOperators

def MonicValue (root : ℂ) (z : ℂ) : ℂ :=
  z - root

/-- For a single root on the closed unit disk, the interior of the unit
disk centered at the root itself lies in the strict unit lemniscate. -/
abbrev statement : Prop :=
  ∀ root : ℂ, ‖root‖ ≤ 1 →
    ∀ z : ℂ, dist z root < 1 → ‖MonicValue root z‖ < 1

theorem target : statement := sorry

end Statements.Erdos1039SingleRootLemniscate
