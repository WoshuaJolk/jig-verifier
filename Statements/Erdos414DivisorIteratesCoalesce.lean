import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos414DivisorIteratesCoalesce

/-- The divisor-count increment map `n ↦ n + τ(n)`. -/
def divisorStep (n : ℕ) : ℕ :=
  n + n.divisors.card

/-- Erdős problem 414: every two positive starting values have intersecting
forward orbits under `n ↦ n + τ(n)`. -/
abbrev statement : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    ∃ i j : ℕ, divisorStep^[i] m = divisorStep^[j] n

theorem target : statement := sorry

end Statements.Erdos414DivisorIteratesCoalesce
