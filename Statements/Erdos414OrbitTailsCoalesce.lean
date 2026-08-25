import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos414OrbitTailsCoalesce

def divisorStep (n : ℕ) : ℕ :=
  n + n.divisors.card

/-- Every orbit coalesces with each of its own tails, giving an infinite
family of pairs satisfying the root conclusion. -/
abbrev statement : Prop :=
  ∀ n k : ℕ, ∃ i j : ℕ,
    divisorStep^[i] n = divisorStep^[j] (divisorStep^[k] n)

theorem target : statement := sorry

end Statements.Erdos414OrbitTailsCoalesce
