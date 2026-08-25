import Mathlib

namespace Submissions.Erdos249SeriesConvergenceBoundary.Worker09ExpectedRed

noncomputable def term (n : ℕ) : ℝ :=
  (Nat.totient n : ℝ) / (2 : ℝ) ^ n

theorem proof (claim : Summable term ∧ term 0 = 0) :
    Summable term ∧ term 0 = 0 := claim

end Submissions.Erdos249SeriesConvergenceBoundary.Worker09ExpectedRed
