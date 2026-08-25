import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Pow

namespace Statements.Erdos463ArbitrarilyLargeWindows

/-- Arbitrarily large least-prime-factor margins occur at some base points.
This is the limsup analogue of the eventual assertion in Erdős Problem 463. -/
abbrev statement : Prop :=
  ∀ B : ℕ, ∃ n m : ℕ,
    (1 < m ∧ ¬m.Prime) ∧
    n + B < m ∧ m < n + m.minFac

theorem target : statement := sorry

end Statements.Erdos463ArbitrarilyLargeWindows
