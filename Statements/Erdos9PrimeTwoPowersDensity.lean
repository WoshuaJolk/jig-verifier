import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

open Filter

namespace Statements.Erdos9PrimeTwoPowersDensity

def Exceptional : Set ℕ :=
  {n | Odd n ∧ ¬ ∃ (p k l : ℕ), Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l}

noncomputable abbrev partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=
  (((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
    ((Set.univ ∩ Set.Iio b).ncard : ℝ)

noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  atTop.limsup fun b : ℕ => partialDensity S b

/-- Erdős Problem 9: the exceptional odd integers have positive
upper natural density. -/
abbrev statement : Prop :=
  0 < upperDensity Exceptional

theorem target : statement := sorry

end Statements.Erdos9PrimeTwoPowersDensity
