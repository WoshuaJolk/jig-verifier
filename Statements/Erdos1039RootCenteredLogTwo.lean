import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Statements.Erdos1039RootCenteredLogTwo

open scoped BigOperators

def MonicValue {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - roots i)

/-- Explicit root-centred lower bound for Erdős Problem 1039: for every
positive degree `n`, every root tuple in the closed unit disk and every
`0 < c < log 2`, the open disk of radius `c / n` around some root lies in the
strict unit lemniscate. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 0 < n → ∀ roots : Fin n → ℂ,
    (∀ i, ‖roots i‖ ≤ 1) →
    ∀ c : ℝ, 0 < c → c < Real.log 2 →
      ∃ j : Fin n, ∀ z : ℂ,
        dist z (roots j) < c / n →
          ‖MonicValue roots z‖ < 1

theorem target : statement := sorry

end Statements.Erdos1039RootCenteredLogTwo
