import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Pointwise

namespace Statements.Erdos52IntegerSumProduct

/-- Erdős Problem 52, the integer sum-product conjecture. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

theorem target : statement := sorry

end Statements.Erdos52IntegerSumProduct
