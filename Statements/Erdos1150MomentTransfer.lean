import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped Polynomial

namespace Statements.Erdos1150MomentTransfer

noncomputable def circleSup (P : ℂ[X]) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖

noncomputable def energy (P : ℂ[X]) : ℝ :=
  ∑ i ∈ P.support, ‖P.coeff i‖ ^ 2

/-- Weighted Parseval, all-moment bounds, and an explicitly conditional
fourth-moment criterion for the full Littlewood fixed-gap conjecture. -/
abbrev statement : Prop :=
  (∀ P Q : ℂ[X], energy (P * Q) ≤ circleSup P ^ 2 * energy Q) ∧
  (∀ (P : ℂ[X]) (k : ℕ),
    energy (P ^ k) ≤ circleSup P ^ (2 * k) ∧
    circleSup P ^ (2 * k) ≤ (k * P.natDegree + 1 : ℝ) * energy (P ^ k)) ∧
  ((∃ δ > (0 : ℝ), ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],
        (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
        P.natDegree = n →
        (1 + δ) * ((n : ℝ) + 1) ^ 2 ≤ energy (P ^ 2)) →
    ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],
        (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
        P.natDegree = n →
        circleSup P > (1 + c) * Real.sqrt n)

theorem target : statement := sorry

end Statements.Erdos1150MomentTransfer
