import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Statements.Erdos510OddFrequenciesPerfectlyNegative

open Real
open scoped Finset

/-- A large exact family for Chowla's problem: at angle `π`, every odd
frequency contributes `-1`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, (∀ n ∈ A, Odd n) →
    ∃ θ : ℝ, ∑ n ∈ A, cos (n * θ) = -(A.card : ℝ)

theorem target : statement := sorry

end Statements.Erdos510OddFrequenciesPerfectlyNegative
