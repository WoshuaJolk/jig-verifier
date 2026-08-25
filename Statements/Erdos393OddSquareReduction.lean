import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorial.Basic

namespace Statements.Erdos393OddSquareReduction

def IsConsecutiveProductFactorial (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ a : ℕ, 1 ≤ a ∧ n.factorial = a * (a + 1)

/-- Exact reduction of the consecutive-product equation to an odd square. -/
abbrev statement : Prop :=
  ∀ n : ℕ, IsConsecutiveProductFactorial n ↔
    1 ≤ n ∧ ∃ b : ℕ, Odd b ∧ b ^ 2 = 4 * n.factorial + 1

theorem target : statement := sorry

end Statements.Erdos393OddSquareReduction
