import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic

namespace Statements.Erdos68SmallTailDenExceedsFactorial

/-- A positive rational strictly smaller than `1/M!` has reduced denominator
strictly larger than `M!`. Consequently its denominator product with any
rational exceeds `M!`, so it cannot satisfy the numerical hypothesis of
factorial-scale separation. -/
abbrev statement : Prop :=
  ∀ y r : ℚ, ∀ M : ℕ,
    1 ≤ M →
    0 < y →
    (y : ℝ) < (1 : ℝ) / M.factorial →
    M.factorial < y.den * r.den

theorem target : statement := sorry

end Statements.Erdos68SmallTailDenExceedsFactorial
