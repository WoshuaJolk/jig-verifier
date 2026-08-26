import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

open scoped BigOperators

namespace Statements.Erdos261IndicesExceedN

/-- In any Erdős--Graham representation of a positive integer `n` by at least two
distinct positive indices, every index strictly exceeds `n`. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), 1 ≤ n → 2 ≤ A.card → (∀ a ∈ A, 1 ≤ a) →
    ((n : ℚ) / (2 : ℚ) ^ n = ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a) →
    ∀ a ∈ A, n < a

theorem target : statement := sorry

end Statements.Erdos261IndicesExceedN
