import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677LengthFourFromPell

/-- Least common multiple of `{n+1, ..., n+k}`, as in Erdős problem 677. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- The length-four case of Erdős problem 677 follows from the Pell core. -/
abbrev statement : Prop :=
  (∀ a b : ℕ, a + 4 ≤ b → ¬ (3 ∣ a) → 3 ∣ b →
      (b ^ 2 + 3 * b + 1) ^ 2 + 2 ≠ 3 * (a ^ 2 + 3 * a + 1) ^ 2) →
    ∀ m n : ℕ, n + 4 ≤ m → lcmInterval m 4 ≠ lcmInterval n 4

theorem target : statement := sorry

end Statements.Erdos677LengthFourFromPell
