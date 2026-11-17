import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos1039UnityUpperBound

open scoped BigOperators

def MonicValue {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - roots i)

/-- The `1/n` order in Erdős Problem 1039 cannot be improved: in every positive
degree `n` some monic polynomial with all roots in the closed unit disk has a
strict unit lemniscate containing no open disk of radius `4 / n`. Every such
disk, whatever its center, meets a point where `|f| ≥ 1`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 0 < n → ∃ roots : Fin n → ℂ,
    (∀ i, ‖roots i‖ ≤ 1) ∧
    ∀ center : ℂ, ∃ z : ℂ,
      dist z center < 4 / n ∧ 1 ≤ ‖MonicValue roots z‖

theorem target : statement := sorry

end Statements.Erdos1039UnityUpperBound
