import Mathlib

namespace Statements.Erdos384InclusiveBoundaryCase

/-- At the smallest source-range boundary, `2` is the required prime divisor. -/
abbrev statement : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose 4 2 ∧ 2 * p ≤ 4

theorem target : statement := sorry

end Statements.Erdos384InclusiveBoundaryCase
