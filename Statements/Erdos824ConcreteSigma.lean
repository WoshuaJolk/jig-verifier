import Mathlib.Data.Nat.Factorization.Divisors

namespace Statements.Erdos824ConcreteSigma

open scoped BigOperators

def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

abbrev statement : Prop :=
  sigma 1 = 1 ∧ sigma 2 = 3 ∧ Nat.Coprime 1 2

theorem target : statement := sorry

end Statements.Erdos824ConcreteSigma
