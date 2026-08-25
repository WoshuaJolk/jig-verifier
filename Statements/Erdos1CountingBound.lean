import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Statements.Erdos1CountingBound

abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    (fun (S : A.powerset) => S.1.sum id).Injective

/-- The elementary counting bound for Erdős Problem 1. -/
abbrev statement : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
    2 ^ A.card ≤ A.card * N + 1

theorem target : statement := sorry

end Statements.Erdos1CountingBound
