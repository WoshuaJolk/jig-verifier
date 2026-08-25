import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Statements.Erdos933SteinerbergerFamilyExactRatio

def twoValuation (n : ℕ) : ℕ := padicValNat 2 (n * (n + 1))

def threeValuation (n : ℕ) : ℕ := padicValNat 3 (n * (n + 1))

/-- On the standard family `n = 2^(3^(r+1))`, the normalized smooth part is
exactly the constant `3 / log 2`; this family alone cannot prove divergence. -/
abbrev statement : Prop :=
  ∀ r : ℕ, let n := 2 ^ (3 ^ (r + 1))
    (((2 ^ twoValuation n * 3 ^ threeValuation n : ℕ) : ℝ) /
      ((n : ℝ) * Real.log (n : ℝ))) = 3 / Real.log 2

theorem target : statement := sorry

end Statements.Erdos933SteinerbergerFamilyExactRatio
