import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

open scoped BigOperators

namespace Statements.Erdos261AllFiniteRepresentations

/-- A positive integer `n` has a representation by at least two distinct
positive indices in the Erdős--Graham equation. -/
def HasRepresentation (n : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    2 ≤ A.card ∧
    (∀ a ∈ A, 1 ≤ a) ∧
    (n : ℚ) / (2 : ℚ) ^ n =
      ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a

/-- The open all-input part of Erdős Problem 261. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → HasRepresentation n

theorem target : statement := sorry

end Statements.Erdos261AllFiniteRepresentations
