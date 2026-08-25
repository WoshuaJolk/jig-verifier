import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Order

namespace Statements.Erdos212DenseRationalDistanceSet

/-- Erdős–Ulam problem: a dense rational-distance set in the plane. -/
abbrev statement : Prop :=
  ∃ u : Set ℂ, Dense u ∧
    u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast

theorem target : statement := sorry

end Statements.Erdos212DenseRationalDistanceSet
