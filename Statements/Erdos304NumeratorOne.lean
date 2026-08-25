import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Defs

namespace Statements.Erdos304NumeratorOne

def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ,
    s.card = k ∧ (∀ n ∈ s, n > 1) ∧
      (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

noncomputable def smallestCollection (a b : ℕ) : ℕ :=
  sInf (unitFractionExpressible a b)

/-- A unit fraction requires exactly one distinct unit-fraction summand. -/
abbrev statement : Prop :=
  ∀ b : ℕ, 1 < b → smallestCollection 1 b = 1

theorem target : statement := sorry

end Statements.Erdos304NumeratorOne
