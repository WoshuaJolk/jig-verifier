import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos1039ConstantAtMostOne

open scoped BigOperators

def MonicValue {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - roots i)

/-- Any constant `c` that works uniformly in Erdős Problem 1039, that is, with
a disk of radius `c / n` in every degree-`n` unit-root lemniscate, is at most
one. The degree-one case already forces this. -/
abbrev statement : Prop :=
  ∀ c : ℝ,
    (∀ n : ℕ, 0 < n → ∀ roots : Fin n → ℂ,
      (∀ i, ‖roots i‖ ≤ 1) →
      ∃ center : ℂ, ∀ z : ℂ,
        dist z center < c / n →
          ‖MonicValue roots z‖ < 1) →
    c ≤ 1

theorem target : statement := sorry

end Statements.Erdos1039ConstantAtMostOne
