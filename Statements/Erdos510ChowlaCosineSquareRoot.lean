import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos510ChowlaCosineSquareRoot

open Real Filter
open scoped Finset

/-- Erdős problem 510 (Chowla's cosine problem): every sufficiently large
finite set of positive frequencies has a cosine sum below a fixed negative
multiple of the square root of its size. -/
abbrev statement : Prop :=
  ∃ (c : ℝ), 0 < c ∧
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, 0 ∉ A → A.card = N →
      ∃ θ : ℝ, ∑ n ∈ A, cos (n * θ) < -c * sqrt N

theorem target : statement := sorry

end Statements.Erdos510ChowlaCosineSquareRoot
