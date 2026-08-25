import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18FourDigitCompression

/-- The exact uniform four-factorial-digit compression suggested by the
small computations: every low four-digit block uses at most three divisors. -/
abbrev statement : Prop :=
  ∀ n m : ℕ, 7 ≤ n →
    m < n * (n - 1) * (n - 2) * (n - 3) →
    ∃ D : Finset ℕ,
      D ⊆ n.factorial.divisors ∧
      D.card ≤ 3 ∧
      m = D.sum id

theorem target : statement := sorry

end Statements.Erdos18FourDigitCompression
