import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos930DisjointIntervalProducts

open Finset

def IsPower (n : ℕ) : Prop :=
  ∃ m l : ℕ, 1 < l ∧ m ^ l = n

/-- Erdős problem 930: for every positive number of disjoint intervals,
sufficiently long positive intervals have a combined product which is not a
perfect power. -/
abbrev statement : Prop :=
  ∀ r : ℕ, 0 < r → ∃ k : ℕ, ∀ I₁ I₂ : Fin r → ℕ,
    (∀ i, 0 < I₁ i ∧ I₁ i + k ≤ I₂ i + 1) →
    (∀ i j, i < j → I₂ i < I₁ j) →
    ¬ IsPower (∏ i : Fin r, ∏ m ∈ Icc (I₁ i) (I₂ i), m)

theorem target : statement := sorry

end Statements.Erdos930DisjointIntervalProducts
