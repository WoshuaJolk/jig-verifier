import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos383BaseCase

def largestPrimeFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

/-- Erdős 383 holds in the boundary case `k=0`. -/
abbrev statement : Prop :=
  {p : ℕ | p.Prime ∧
    largestPrimeFactor (∏ i ∈ Finset.Icc 0 0, (p ^ 2 + i)) = p}.Infinite

theorem target : statement := sorry

end Statements.Erdos383BaseCase
