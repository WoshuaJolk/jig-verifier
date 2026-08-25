import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

open scoped BigOperators

namespace Statements.Erdos261SmallRepresentations

def HasRepresentation (n : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    2 ≤ A.card ∧
    (∀ a ∈ A, 1 ≤ a) ∧
    (n : ℚ) / (2 : ℚ) ^ n =
      ∑ a ∈ A, (a : ℚ) / (2 : ℚ) ^ a

/-- Two exact small instances, including the endpoint `n = 1`. -/
abbrev statement : Prop :=
  HasRepresentation 1 ∧ HasRepresentation 4

theorem target : statement := sorry

end Statements.Erdos261SmallRepresentations
