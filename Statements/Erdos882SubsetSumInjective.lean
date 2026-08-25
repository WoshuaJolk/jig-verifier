import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos882SubsetSumInjective

open Finset

def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.erase ∅).image fun B => B.sum id

def DivisibilityAntichain (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ∣ y → x = y

/-- The divisibility-antichain hypothesis forces all subset sums to be
represented uniquely. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ,
    A ⊆ Icc 1 n →
    DivisibilityAntichain (nonemptySubsetSums A) →
    ∀ B ⊆ A, ∀ C ⊆ A,
      B.sum id = C.sum id → B = C

theorem target : statement := sorry

end Statements.Erdos882SubsetSumInjective
