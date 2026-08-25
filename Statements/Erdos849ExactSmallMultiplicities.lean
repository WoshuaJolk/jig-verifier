import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card

namespace Statements.Erdos849ExactSmallMultiplicities

def occurrences (a : ℕ) : Set (ℕ × ℕ) :=
  {(n, k) | 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.choose n k = a}

/-- Exact lower-half multiplicities one and two occur at values 2 and 6. -/
abbrev statement : Prop :=
  (occurrences 2).ncard = 1 ∧ (occurrences 6).ncard = 2

theorem target : statement := sorry

end Statements.Erdos849ExactSmallMultiplicities
