import Mathlib

namespace Statements.Erdos384StrictPrimeDivisorRefutation

abbrev IsErdos384Exception (n k : ℕ) : Prop :=
  n = 7 ∧ (k = 3 ∨ k = 4)

/-- Literal strict formulation of Erdős Problem 384, which is false at `n=4`, `k=2`. -/
abbrev statement : Prop :=
  ¬ (∀ n k : ℕ, 1 < k → k < n - 1 → ¬ IsErdos384Exception n k →
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose n k ∧ 2 * p < n)

theorem target : statement := sorry

end Statements.Erdos384StrictPrimeDivisorRefutation
