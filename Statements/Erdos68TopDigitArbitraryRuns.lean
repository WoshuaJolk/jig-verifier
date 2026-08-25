import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Statements.Erdos68TopDigitArbitraryRuns

/-- The perturbed fractional recurrence admits maximal digits for arbitrarily
long consecutive finite runs. Therefore positivity of the perturbations and
shrinking interval iteration alone cannot yield a universal run bound. -/
abbrev statement : Prop :=
  ∀ M : ℕ, 3 ≤ M → ∀ L : ℕ,
    ∃ f : ℕ → ℝ,
      (∀ i : ℕ, i ≤ L → 0 < f i ∧ f i < 1) ∧
      (∀ i : ℕ, i < L →
        let m := M + i
        ⌊(m : ℝ) * f i + 1 / (m.factorial - 1 : ℕ)⌋ =
            (m - 1 : ℕ) ∧
          f (i + 1) =
            (m : ℝ) * f i + 1 / (m.factorial - 1 : ℕ) -
              (m - 1 : ℕ))

theorem target : statement := sorry

end Statements.Erdos68TopDigitArbitraryRuns
