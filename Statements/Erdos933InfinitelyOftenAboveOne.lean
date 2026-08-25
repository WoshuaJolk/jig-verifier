import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Statements.Erdos933InfinitelyOftenAboveOne

def twoValuation (n : ℕ) : ℕ := padicValNat 2 (n * (n + 1))

def threeValuation (n : ℕ) : ℕ := padicValNat 3 (n * (n + 1))

/-- The known lower-bound family: the 2,3-smooth part of n(n+1) exceeds
n log n for infinitely many n. -/
abbrev statement : Prop :=
  Set.Infinite {n : ℕ |
    ((2 ^ twoValuation n * 3 ^ threeValuation n : ℕ) : ℝ) >
      (n : ℝ) * Real.log (n : ℝ)}

theorem target : statement := sorry

end Statements.Erdos933InfinitelyOftenAboveOne
