import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped Polynomial

namespace Statements.Erdos1150LittlewoodUniformGap

/-- Erdős Problem 1150: every sufficiently high-degree Littlewood polynomial has unit-circle supremum uniformly separated above the Parseval scale. -/
abbrev statement : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
    ∀ P : ℂ[X],
      (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
      P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1,
          ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n

theorem target : statement := sorry

end Statements.Erdos1150LittlewoodUniformGap
