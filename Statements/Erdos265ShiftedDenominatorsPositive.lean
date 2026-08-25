import Mathlib.Data.Real.Basic

namespace Statements.Erdos265ShiftedDenominatorsPositive

/-- The lower-bound convention in the Erdős 265 verifier makes both
Ahmes-series denominators strictly positive. -/
abbrev statement : Prop :=
  ∀ a : ℕ → ℕ, (∀ n, 2 ≤ a n) →
    ∀ n, 0 < a n ∧ 0 < a n - 1

theorem target : statement := sorry

end Statements.Erdos265ShiftedDenominatorsPositive
