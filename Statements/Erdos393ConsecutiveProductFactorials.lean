import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Card

namespace Statements.Erdos393ConsecutiveProductFactorials

def IsConsecutiveProductFactorial (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ a : ℕ, 1 ≤ a ∧ n.factorial = a * (a + 1)

/-- Erdős Problem 393, explicit open subquestion: infinitely many factorials
are products of two consecutive positive integers. -/
abbrev statement : Prop :=
  Set.Infinite {n : ℕ | IsConsecutiveProductFactorial n}

theorem target : statement := sorry

end Statements.Erdos393ConsecutiveProductFactorials
