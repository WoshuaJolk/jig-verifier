import Mathlib.Analysis.Polynomial.Fourier

open scoped Polynomial

namespace Statements.Erdos1150EndpointBoundary

/-- An additive improvement over Parseval, not a uniform multiplicative gap. -/
abbrev statement : Prop :=
  ∀ (P : ℂ[X]) (n : ℕ),
    (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
    P.natDegree = n → 0 < n →
      ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ ≥
        Real.sqrt ((n : ℝ) + 3)

theorem target : statement := sorry

end Statements.Erdos1150EndpointBoundary
