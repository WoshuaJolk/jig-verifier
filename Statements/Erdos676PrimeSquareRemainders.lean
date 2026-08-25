import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter

namespace Statements.Erdos676PrimeSquareRemainders

/-- Erdős Problem 676. -/
abbrev statement : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∃ p a b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b

theorem target : statement := sorry

end Statements.Erdos676PrimeSquareRemainders
