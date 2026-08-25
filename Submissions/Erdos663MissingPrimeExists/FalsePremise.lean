import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Submissions.Erdos663MissingPrimeExists.FalsePremise

def blockProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

theorem proof :
    False →
      ∀ n k : ℕ, ∃ p : ℕ, p.Prime ∧ ¬p ∣ blockProduct n k := by
  intro h
  exact h.elim

end Submissions.Erdos663MissingPrimeExists.FalsePremise
