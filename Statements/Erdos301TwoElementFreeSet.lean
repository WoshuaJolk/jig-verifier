import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos301TwoElementFreeSet

def IsReciprocalEquationFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ¬∃ B : Finset ℕ, B.Nonempty ∧ B ⊆ A.erase a ∧
    ((a : ℝ)⁻¹ = ∑ b ∈ B, (b : ℝ)⁻¹)

/-- The set `{2,3}` has no reciprocal equal to a sum of reciprocals of
distinct other members. -/
abbrev statement : Prop :=
  IsReciprocalEquationFree {2, 3}

theorem target : statement := sorry

end Statements.Erdos301TwoElementFreeSet
