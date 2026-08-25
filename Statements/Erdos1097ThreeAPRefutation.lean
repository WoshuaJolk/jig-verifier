import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

namespace Statements.Erdos1097ThreeAPRefutation

/-- Nonzero common differences of three-term arithmetic progressions in `A`. -/
def CommonDifferences (A : Finset ℤ) : Set ℤ :=
  {d : ℤ | d ≠ 0 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    b - a = d ∧ c - b = d}

/-- The Erdős–Spencer `O(n^(3/2))` prediction is false. -/
abbrev statement : Prop :=
  ¬ ∃ C > (0 : ℝ), ∀ A : Finset ℤ,
    (CommonDifferences A).ncard ≤ C * (A.card : ℝ) ^ (3 / 2 : ℝ)

theorem target : statement := sorry

end Statements.Erdos1097ThreeAPRefutation
