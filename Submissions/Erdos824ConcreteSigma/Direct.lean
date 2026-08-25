import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos824ConcreteSigma.Direct

open scoped BigOperators

def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

theorem proof : sigma 1 = 1 ∧ sigma 2 = 3 ∧ Nat.Coprime 1 2 := by
  decide +kernel

end Submissions.Erdos824ConcreteSigma.Direct
