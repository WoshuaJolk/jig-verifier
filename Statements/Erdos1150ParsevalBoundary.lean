import Mathlib.Analysis.Polynomial.Fourier

open scoped Polynomial

namespace Statements.Erdos1150ParsevalBoundary

/-- Parseval's exact boundary for Littlewood polynomials. -/
abbrev statement : Prop :=
  ∀ P : ℂ[X], ∀ n : ℕ,
    (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
    P.natDegree = n →
      ⨆ z : Metric.sphere (0 : ℂ) 1,
        ‖P.eval (z : ℂ)‖ ≥ Real.sqrt (n + 1)

theorem target : statement := sorry

end Statements.Erdos1150ParsevalBoundary
