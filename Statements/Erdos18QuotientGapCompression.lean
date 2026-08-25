import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18QuotientGapCompression

/-- A divisor of `(n-1)!` less than one radix step below the quotient gives a
nonlocal three-divisor representation after restoring the final radix digit. -/
abbrev statement : Prop :=
  ∀ n m q r x : ℕ, 7 ≤ n →
    m = q * n + r →
    r < n →
    n ≤ x →
    x ≤ q →
    q < x + n →
    x ∣ (n - 1).factorial →
    ∃ D : Finset ℕ,
      D ⊆ n.factorial.divisors ∧
      D.card ≤ 3 ∧
      m = D.sum id

theorem target : statement := sorry

end Statements.Erdos18QuotientGapCompression
