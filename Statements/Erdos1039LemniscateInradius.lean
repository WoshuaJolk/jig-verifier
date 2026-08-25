import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos1039LemniscateInradius

open scoped BigOperators

def MonicValue {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - roots i)

/-- The explicit `rho(f) >> 1/n` question in Erdős Problem 1039,
written directly as existence of an inscribed disk. -/
abbrev statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 0 < n → ∀ roots : Fin n → ℂ,
      (∀ i, ‖roots i‖ ≤ 1) →
      ∃ center : ℂ, ∀ z : ℂ,
        dist z center < c / n →
          ‖MonicValue roots z‖ < 1

theorem target : statement := sorry

end Statements.Erdos1039LemniscateInradius
