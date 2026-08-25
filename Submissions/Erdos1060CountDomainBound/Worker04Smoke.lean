import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Finset
open scoped ArithmeticFunction.sigma

namespace Submissions.Erdos1060CountDomainBound.Worker04Smoke

def solutionCount (n : ℕ) : ℕ :=
  #{k ≤ n | k * σ 1 k = n}

theorem proof : ∀ n : ℕ, solutionCount n ≤ n + 1 := by
  intro n
  exact (card_filter_le _ _).trans_eq (by simp)

end Submissions.Erdos1060CountDomainBound.Worker04Smoke
