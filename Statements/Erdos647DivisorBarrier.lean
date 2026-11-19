import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos647DivisorBarrier

/-- Erdős Problem 647 (Erdős and Selfridge). Writing `τ(m)` for the number of divisors of
`m`, is there some `n > 24` with `max_{m < n} (m + τ(m)) ≤ n + 2`? The maximum over `m < n`
being at most `n + 2` is stated as a bound on every `m < n`. `Nat.divisors 0 = ∅`, so the
term `m = 0` contributes `0` and constrains nothing. -/
abbrev statement : Prop :=
  ∃ n : ℕ, 24 < n ∧ ∀ m : ℕ, m < n → m + m.divisors.card ≤ n + 2

theorem target : statement := sorry

end Statements.Erdos647DivisorBarrier
