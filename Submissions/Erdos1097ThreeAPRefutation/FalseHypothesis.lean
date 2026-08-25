import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

namespace Submissions.Erdos1097ThreeAPRefutation.FalseHypothesis

def CommonDifferences (A : Finset ℤ) : Set ℤ :=
  {d : ℤ | d ≠ 0 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    b - a = d ∧ c - b = d}

theorem proof :
    False →
      ¬ ∃ C > (0 : ℝ), ∀ A : Finset ℤ,
        (CommonDifferences A).ncard ≤
          C * (A.card : ℝ) ^ (3 / 2 : ℝ) :=
  False.elim

end Submissions.Erdos1097ThreeAPRefutation.FalseHypothesis
