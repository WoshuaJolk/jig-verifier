import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

namespace Submissions.Erdos158FinitePairBound.Control

open Finset

def B2 (g : ℕ) (A : Set ℕ) : Prop :=
  ∀ n, {x : ℕ × ℕ |
    x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ g

abbrev claimedStatement : Prop :=
  ∀ (S : Finset ℕ) (N : ℕ),
    (∀ a ∈ S, a < N) → B2 2 (S : Set ℕ) →
      #((S ×ˢ S).filter fun p => p.1 ≤ p.2) ≤ 4 * N

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos158FinitePairBound.Control
