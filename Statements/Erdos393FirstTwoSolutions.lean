import Mathlib.Data.Nat.Factorial.Basic

namespace Statements.Erdos393FirstTwoSolutions

def IsConsecutiveProductFactorial (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ a : ℕ, 1 ≤ a ∧ n.factorial = a * (a + 1)

/-- The first two positive examples are `2! = 1·2` and `3! = 2·3`. -/
abbrev statement : Prop :=
  IsConsecutiveProductFactorial 2 ∧ IsConsecutiveProductFactorial 3

theorem target : statement := sorry

end Statements.Erdos393FirstTwoSolutions
