import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Statements.Erdos663MissingPrimeExists

def blockProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

abbrev statement : Prop :=
  ∀ n k : ℕ, ∃ p : ℕ, p.Prime ∧ ¬p ∣ blockProduct n k

theorem target : statement := sorry

end Statements.Erdos663MissingPrimeExists
