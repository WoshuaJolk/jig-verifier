import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open scoped Pointwise
namespace Statements.Erdos52KnownRange
/-- Known range only: this is not the full integer sum-product conjecture. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, (2 : ℝ) / 3 < ε → ε < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)
theorem target : statement := sorry
end Statements.Erdos52KnownRange
