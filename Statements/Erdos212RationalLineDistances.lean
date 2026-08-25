import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Order

namespace Statements.Erdos212RationalLineDistances

/-- Rational points embedded in the real axis have rational pairwise distance. -/
abbrev statement : Prop :=
  (Set.range fun q : ℚ => (q : ℂ)).Pairwise
    fun z₁ z₂ => dist z₁ z₂ ∈ Set.range Rat.cast

theorem target : statement := sorry

end Statements.Erdos212RationalLineDistances
