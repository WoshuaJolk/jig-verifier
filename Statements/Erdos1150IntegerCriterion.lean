import Mathlib.Analysis.Polynomial.Fourier

open scoped Polynomial

namespace Statements.Erdos1150IntegerCriterion

-- Deliberately expanded: this is exactly Jig #249's original root type.
abbrev originalRoot : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
    ∀ P : ℂ[X],
      (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
      P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1,
          ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n

def integerEnergy (A : ℤ[X]) : ℤ :=
  ∑ i ∈ A.support, A.coeff i ^ 2

/-- One positive integer q, chosen before the eventual degree and sign polynomial.
Every quantity in the final strict inequality is an integer. -/
abbrev integerCriterion : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∀ᶠ n in Filter.atTop,
    ∀ A : ℤ[X],
      (∀ i ≤ A.natDegree, A.coeff i = -1 ∨ A.coeff i = 1) →
      A.natDegree = n →
        ((q : ℤ) + 1) ^ n * ((n : ℤ) + 1) ^ n <
          (q : ℤ) ^ n * integerEnergy (A ^ n)

/-- Reformulation of the entire fixed-gap question; neither side is asserted here. -/
abbrev statement : Prop := originalRoot ↔ integerCriterion

theorem target : statement := sorry

end Statements.Erdos1150IntegerCriterion
