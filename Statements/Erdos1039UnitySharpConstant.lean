import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Statements.Erdos1039UnitySharpConstant

open scoped BigOperators

def MonicValue {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - roots i)

/-- Upper bound for Erdős Problem 1039 with the asymptotically sharp constant:
in every positive degree `n` some monic polynomial with all roots in the closed
unit disk has a strict unit lemniscate containing no open disk of radius
`(π / 2) (1 + 1 / n) / n`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 0 < n → ∃ roots : Fin n → ℂ,
    (∀ i, ‖roots i‖ ≤ 1) ∧
    ∀ center : ℂ, ∃ z : ℂ,
      dist z center < Real.pi / 2 * (1 + 1 / n) / n ∧ 1 ≤ ‖MonicValue roots z‖

theorem target : statement := sorry

end Statements.Erdos1039UnitySharpConstant
