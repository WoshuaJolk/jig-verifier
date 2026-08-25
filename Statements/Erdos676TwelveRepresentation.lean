import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos676TwelveRepresentation

/-- Twelve has the required prime-square representation. -/
abbrev statement : Prop :=
  ∃ p a b : ℕ,
    p.Prime ∧ 1 ≤ a ∧ b < p ∧ 12 = a * p ^ 2 + b

theorem target : statement := sorry

end Statements.Erdos676TwelveRepresentation
