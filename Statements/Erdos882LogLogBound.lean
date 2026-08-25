import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos882LogLogBound

open Finset

def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.erase ∅).image fun B => B.sum id

def DivisibilityAntichain (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ∣ y → x = y

abbrev AntichainInjective : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ,
    A ⊆ Icc 1 n →
    DivisibilityAntichain (nonemptySubsetSums A) →
    ∀ B ⊆ A, ∀ C ⊆ A,
      B.sum id = C.sum id → B = C

abbrev InjectiveCountingBound : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ,
    A ⊆ Icc 1 n →
    (∀ B ∈ A.powerset, ∀ C ∈ A.powerset,
      B.sum id = C.sum id → B = C) →
    2 ^ A.card ≤ A.card * n + 1

/-- The two green combinatorial statements imply the explicit
`log₂ n + log₂ log₂ n + O(1)` upper bound. -/
abbrev statement : Prop :=
  AntichainInjective → InjectiveCountingBound →
    ∀ n : ℕ, ∀ A : Finset ℕ, 2 ≤ n →
      A ⊆ Icc 1 n →
      DivisibilityAntichain (nonemptySubsetSums A) →
      A.card ≤ Nat.log 2 n + Nat.log 2 (2 * Nat.log 2 n + 4) + 2

theorem target : statement := sorry

end Statements.Erdos882LogLogBound
