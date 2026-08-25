import Mathlib.Data.Nat.Prime.Factorial

namespace Statements.Erdos68LargePrimeDivisor

/-- Every denominator `n! - 1` from `n = 3` onward has a prime factor
strictly larger than `n`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ n.factorial - 1

theorem target : statement := sorry

end Statements.Erdos68LargePrimeDivisor
