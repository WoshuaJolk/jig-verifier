import Mathlib

namespace Statements.Erdos698GrowingBinomialGCD

/-- Erdős Problem 698: binomial-coefficient gcds admit a uniform diverging lower bound. -/
abbrev statement : Prop :=
  ∃ h : ℕ → ℕ, Filter.Tendsto h Filter.atTop Filter.atTop ∧
    ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
      h n ≤ Nat.gcd (n.choose i) (n.choose j)

theorem target : statement := sorry

end Statements.Erdos698GrowingBinomialGCD
