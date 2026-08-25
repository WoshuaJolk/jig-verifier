import Mathlib.Data.Int.Basic

namespace Statements.Erdos243NonnegativeCenteredState

/-- In an exact product-cleared reciprocal-tail orbit, a globally nonnegative
centered state forces eventual Sylvester recurrence. -/
abbrev statement : Prop :=
  ∀ (a D C E : ℕ → ℕ),
    (∀ n, 1 < a n) →
    (∀ n, 0 < C n) →
    (∀ n, D (n + 1) = a n * D n) →
    (∀ n, C (n + 1) + D n = a n * C n) →
    (∀ n, (E n : ℤ) =
      (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ)) →
    ∃ N, ∀ n, N ≤ n → a (n + 1) = a n ^ 2 - a n + 1

theorem target : statement := sorry

end Statements.Erdos243NonnegativeCenteredState
