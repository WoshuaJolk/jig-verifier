import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Pointwise

namespace Statements.Erdos52LinearLowerBound

/-- A uniform linear lower bound for the integer sum-product maximum. -/
abbrev statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ)

theorem target : statement := sorry

end Statements.Erdos52LinearLowerBound
