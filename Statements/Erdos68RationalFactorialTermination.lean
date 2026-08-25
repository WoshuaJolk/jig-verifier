import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Statements.Erdos68RationalFactorialTermination

/-- Every rational has an explicit terminating factorial expansion: its
denominator index suffices, all later canonical factorial digits vanish, and
the preceding factorial scale is integral. -/
abbrev statement : Prop :=
  ∀ q : ℚ,
    let N := q.den
    (∃ z : ℤ, (N.factorial : ℝ) * (q : ℝ) = z) ∧
    (∀ m : ℕ, N + 1 ≤ m →
      ⌊(m.factorial : ℝ) * (q : ℝ)⌋ -
        (m : ℤ) * ⌊((m - 1).factorial : ℝ) * (q : ℝ)⌋ = 0)

theorem target : statement := sorry

end Statements.Erdos68RationalFactorialTermination
