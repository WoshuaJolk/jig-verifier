import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos244ThreeRepresentable

def representable (C : ℝ) : Set ℕ :=
  {x | ∃ p k : ℕ, p.Prime ∧ x = p + ⌊C ^ k⌋₊}

/-- Three is represented for base two. -/
abbrev statement : Prop :=
  3 ∈ representable 2

theorem target : statement := sorry

end Statements.Erdos244ThreeRepresentable
