import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas

namespace Statements.Erdos68TwoTermDenExceedsFactorial

/-- The consecutive two-term tail `1/(n!−1)+1/((n+1)!−1)` has reduced
denominator strictly larger than `(n+1)!`, so it cannot satisfy the
numerical hypothesis of factorial-scale separation. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ((1 : ℚ) / (n.factorial - 1 : ℕ) +
        1 / ((n + 1).factorial - 1 : ℕ)).den >
      (n + 1).factorial

theorem target : statement := sorry

end Statements.Erdos68TwoTermDenExceedsFactorial
