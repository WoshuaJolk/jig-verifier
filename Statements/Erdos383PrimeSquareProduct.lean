import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Nat

def maxPrimeFac383 (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

end Nat

namespace Statements.Erdos383PrimeSquareProduct

/-- Erdős Problem 383: for every `k`, infinitely many primes `p` have `p`
as the largest prime factor of `∏ i ∈ [0,k], (p²+i)`. -/
abbrev statement : Prop :=
  ∀ k, {p : ℕ | p.Prime ∧
    Nat.maxPrimeFac383 (∏ i ∈ Finset.Icc 0 k, (p ^ 2 + i)) = p}.Infinite

theorem target : statement := sorry

end Statements.Erdos383PrimeSquareProduct
