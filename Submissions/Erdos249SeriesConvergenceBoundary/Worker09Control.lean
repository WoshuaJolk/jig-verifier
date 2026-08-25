import Mathlib

namespace Submissions.Erdos249SeriesConvergenceBoundary.Worker09Control

noncomputable def term (n : ℕ) : ℝ :=
  (Nat.totient n : ℝ) / (2 : ℝ) ^ n

theorem proof (h : Summable term ∧ term 0 = 0) :
    Summable term ∧ term 0 = 0 := h

end Submissions.Erdos249SeriesConvergenceBoundary.Worker09Control
