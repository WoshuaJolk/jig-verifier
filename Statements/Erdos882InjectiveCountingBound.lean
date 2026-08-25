import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos882InjectiveCountingBound

open Finset

/-- Injective subset sums in `{1,…,n}` obey the standard counting bound. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ,
    A ⊆ Icc 1 n →
    (∀ B ∈ A.powerset, ∀ C ∈ A.powerset,
      B.sum id = C.sum id → B = C) →
    2 ^ A.card ≤ A.card * n + 1

theorem target : statement := sorry

end Statements.Erdos882InjectiveCountingBound
