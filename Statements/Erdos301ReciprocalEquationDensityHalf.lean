import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos301ReciprocalEquationDensityHalf

open Filter

def IsReciprocalEquationFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ¬∃ B : Finset ℕ, B.Nonempty ∧ B ⊆ A.erase a ∧
    ((a : ℝ)⁻¹ = ∑ b ∈ B, (b : ℝ)⁻¹)

/-- The central asymptotic conjecture in Erdős Problem 301: every subset of
`[1,N]` avoiding a reciprocal represented as a sum of reciprocals of other
distinct members has density at most one half. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      IsReciprocalEquationFree A →
        (A.card : ℝ) ≤ (1 / 2 + ε) * N

theorem target : statement := sorry

end Statements.Erdos301ReciprocalEquationDensityHalf
