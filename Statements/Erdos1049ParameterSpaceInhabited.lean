import Mathlib.Data.Rat.Defs

namespace Statements.Erdos1049ParameterSpaceInhabited

/-- The nonintegral rational parameter range in Chowla's conjecture is nonempty. -/
abbrev statement : Prop := ∃ t : ℚ, t > 1

theorem target : statement := sorry

end Statements.Erdos1049ParameterSpaceInhabited
