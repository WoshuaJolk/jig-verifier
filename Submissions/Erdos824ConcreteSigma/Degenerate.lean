import Mathlib.Data.Nat.Factorization.Divisors

namespace Submissions.Erdos824ConcreteSigma.Degenerate

open scoped BigOperators

def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

theorem proof : False →
    sigma 1 = 1 ∧ sigma 2 = 3 ∧ Nat.Coprime 1 2 := False.elim

end Submissions.Erdos824ConcreteSigma.Degenerate
