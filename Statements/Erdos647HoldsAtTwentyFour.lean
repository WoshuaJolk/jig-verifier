import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos647HoldsAtTwentyFour

/-- The barrier condition of Erdős Problem 647 holds at `n = 24`, and fails at `n = 25`:
the body of the root `Erdos647DivisorBarrier` instantiated at its boundary. -/
abbrev statement : Prop :=
  (∀ m : ℕ, m < 24 → m + m.divisors.card ≤ 24 + 2) ∧
    ¬ (∀ m : ℕ, m < 25 → m + m.divisors.card ≤ 25 + 2)

theorem target : statement := sorry

end Statements.Erdos647HoldsAtTwentyFour
