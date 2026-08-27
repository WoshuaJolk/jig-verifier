import Mathlib.Data.Nat.Defs

namespace Statements.Erdos677PellCore

/-- The arithmetic core of the length-four case of Erdős problem 677.
With `A = a²+3a+1` and `B = b²+3b+1`, the Pell equation `B² + 2 = 3A²` has no
solution with `b ≥ a + 4`, `3 ∤ a` and `3 ∣ b`. -/
abbrev statement : Prop :=
  ∀ a b : ℕ, a + 4 ≤ b → ¬ (3 ∣ a) → 3 ∣ b →
    (b ^ 2 + 3 * b + 1) ^ 2 + 2 ≠ 3 * (a ^ 2 + 3 * a + 1) ^ 2

theorem target : statement := sorry

end Statements.Erdos677PellCore
