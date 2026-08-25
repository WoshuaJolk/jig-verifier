import Mathlib.Analysis.PSeries

/-!
# A quadratic-growth regime of Erdős problem 12

For an increasing Property P sequence, the pointwise lower bound
`(n+1)^2 ≤ a_n` already forces reciprocal summability by comparison with the
convergent p-series.  This records a precise sufficient condition and isolates
the unresolved regime: Property P must itself be used to derive enough growth
or reciprocal-mass decay.
-/

namespace Statements.Erdos12QuadraticGrowth

abbrev statement : Prop :=
  ∀ u : ℕ → ℕ,
    StrictMono u →
    (∀ i j k : ℕ, i < j → i < k → u i ∣ u j + u k → j = k) →
    (∀ n : ℕ, (n + 1) ^ 2 ≤ u n) →
    Summable (fun n : ℕ => (1 : ℝ) / (u n : ℝ))

theorem target : statement := sorry

end Statements.Erdos12QuadraticGrowth
