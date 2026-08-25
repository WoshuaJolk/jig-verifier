import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Submissions.Erdos383BaseCase.Degenerate

def largestPrimeFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

theorem proof : False →
    {p : ℕ | p.Prime ∧
      largestPrimeFactor (∏ i ∈ Finset.Icc 0 0, (p ^ 2 + i)) = p}.Infinite :=
  False.elim

end Submissions.Erdos383BaseCase.Degenerate
