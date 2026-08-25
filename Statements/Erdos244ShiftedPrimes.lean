import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos244ShiftedPrimes

def representable (C : ℝ) : Set ℕ :=
  {x | ∃ p k : ℕ, p.Prime ∧ x = p + ⌊C ^ k⌋₊}

/-- The zero-exponent slice contains every prime shifted by one. -/
abbrev statement : Prop :=
  ∀ C : ℝ, ∀ p : ℕ, p.Prime → p + 1 ∈ representable C

theorem target : statement := sorry

end Statements.Erdos244ShiftedPrimes
