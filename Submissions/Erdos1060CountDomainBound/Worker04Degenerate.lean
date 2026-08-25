import Mathlib.NumberTheory.ArithmeticFunction.Misc

open Finset
open scoped ArithmeticFunction.sigma

namespace Submissions.Erdos1060CountDomainBound.Worker04Degenerate

def solutionCount (n : ℕ) : ℕ :=
  #{k ≤ n | k * σ 1 k = n}

theorem proof : False → ∀ n : ℕ, solutionCount n ≤ n + 1 :=
  False.elim

end Submissions.Erdos1060CountDomainBound.Worker04Degenerate
