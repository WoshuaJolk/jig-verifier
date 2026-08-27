import Mathlib.Data.Nat.Defs

namespace Statements.Erdos677TetrahedralCore

/-- The arithmetic core of the length-three case of Erdős problem 677:
the cubic equation `v³ - v = 2(u³ - u)`, written without truncated subtraction,
has no solution with `v ≥ u + 3`. -/
abbrev statement : Prop :=
  ∀ u v : ℕ, u + 3 ≤ v → v ^ 3 + 2 * u ≠ 2 * u ^ 3 + v

theorem target : statement := sorry

end Statements.Erdos677TetrahedralCore
