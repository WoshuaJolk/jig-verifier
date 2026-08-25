import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.LiminfLimsup

open Filter

namespace Statements.Erdos244RomanoffRealPowers

/-- Lower natural density, written explicitly for subsets of `ℕ`. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  liminf (fun b : ℕ => ((S ∩ Set.Iio b).ncard : ℝ) / ((Set.univ ∩ Set.Iio b).ncard : ℝ)) atTop

/-- Integers represented as a prime plus the floor of a real power. -/
def representable (C : ℝ) : Set ℕ :=
  {x | ∃ p k : ℕ, p.Prime ∧ x = p + ⌊C ^ k⌋₊}

/-- Erdős Problem 244. -/
abbrev statement : Prop :=
  ∀ C > (1 : ℝ), 0 < lowerDensity (representable C)

theorem target : statement := sorry

end Statements.Erdos244RomanoffRealPowers
