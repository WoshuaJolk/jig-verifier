import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

namespace Statements.Erdos304OneHalf

def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ,
    s.card = k ∧ (∀ n ∈ s, n > 1) ∧
      (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

/-- One half is represented by one unit fraction. -/
abbrev statement : Prop :=
  1 ∈ unitFractionExpressible 1 2

theorem target : statement := sorry

end Statements.Erdos304OneHalf
