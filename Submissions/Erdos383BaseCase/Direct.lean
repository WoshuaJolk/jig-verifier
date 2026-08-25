import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos383BaseCase.Direct

def largestPrimeFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

theorem proof :
    {p : ℕ | p.Prime ∧
      largestPrimeFactor (∏ i ∈ Finset.Icc 0 0, (p ^ 2 + i)) = p}.Infinite := by
  refine Nat.infinite_setOfPred_prime.mono ?_
  intro p hp
  refine ⟨hp, ?_⟩
  simp [largestPrimeFactor, hp.ne_one, hp.primeFactorsList_pow,
    List.getLastI]

end Submissions.Erdos383BaseCase.Direct
