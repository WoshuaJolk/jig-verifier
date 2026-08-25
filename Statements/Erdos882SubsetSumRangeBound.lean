import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos882SubsetSumRangeBound

open Finset

/-- Every subset sum of `A ⊆ {1,…,n}` lies below `|A|n`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ A B : Finset ℕ,
    A ⊆ Icc 1 n → B ⊆ A →
    B.sum id ≤ A.card * n

theorem target : statement := sorry

end Statements.Erdos882SubsetSumRangeBound
