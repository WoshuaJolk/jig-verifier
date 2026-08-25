import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos68FactorialDigitFormula

/-- The canonical factorial digit lies in its radix range; a positive tail
preserves the relevant floor when it is below the fractional margin; and an
already-integral preceding scale forces the digit to vanish. -/
abbrev statement : Prop :=
  (∀ m : ℕ, 1 ≤ m → ∀ x : ℝ,
    let a : ℤ :=
      ⌊(m.factorial : ℝ) * x⌋ -
        (m : ℤ) * ⌊((m - 1).factorial : ℝ) * x⌋
    0 ≤ a ∧ a < m) ∧
  (∀ y t : ℝ, 0 ≤ t →
    t < (⌊y⌋ : ℝ) + 1 - y →
    ⌊y + t⌋ = ⌊y⌋) ∧
  (∀ m : ℕ, 1 ≤ m → ∀ x : ℝ, ∀ z : ℤ,
    ((m - 1).factorial : ℝ) * x = z →
    ⌊(m.factorial : ℝ) * x⌋ -
        (m : ℤ) * ⌊((m - 1).factorial : ℝ) * x⌋ = 0)

theorem target : statement := sorry

end Statements.Erdos68FactorialDigitFormula
