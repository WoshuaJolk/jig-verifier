import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos727FactorialSquareDivisibility

/-- Erdős Problem 727: for every fixed `k ≥ 2`, there should be infinitely
many `n` for which the square of `(n+k)!` divides `(2n)!`. -/
abbrev statement : Prop :=
  ∀ k ≥ 2,
    Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)}

/-- Open target; submissions prove `statement` in their own module. -/
theorem target : statement := sorry

end Statements.Erdos727FactorialSquareDivisibility
