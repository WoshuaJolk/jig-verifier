import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

namespace Statements.Erdos158FinitePairBound

open Finset

def B2 (g : ℕ) (A : Set ℕ) : Prop :=
  ∀ n, {x : ℕ × ℕ |
    x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ g

/-- A finite `B₂[2]` set below `N` has at most `4N` unordered pairs.
This is the elementary quadratic counting bound underlying Problem 158. -/
abbrev statement : Prop :=
  ∀ (S : Finset ℕ) (N : ℕ),
    (∀ a ∈ S, a < N) → B2 2 (S : Set ℕ) →
      #((S ×ˢ S).filter fun p => p.1 ≤ p.2) ≤ 4 * N

theorem target : statement := sorry

end Statements.Erdos158FinitePairBound
