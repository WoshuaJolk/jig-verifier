import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos279PrimeCongruenceCover

/-- Erdős Problem 279: choose one residue class modulo every prime so that,
for each `k ≥ 3`, every sufficiently large integer lies at least `k` prime
steps beyond the selected representative for some prime. -/
abbrev statement : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ a : ℕ → ℕ, ∃ N : ℕ,
      (∀ p : ℕ, p.Prime → a p < p) ∧
      ∀ n ≥ N, ∃ p : ℕ, ∃ t ≥ k,
        p.Prime ∧ n = a p + t * p

theorem target : statement := sorry

end Statements.Erdos279PrimeCongruenceCover
