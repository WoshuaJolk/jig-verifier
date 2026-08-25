import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

open Asymptotics Filter
open scoped Real

namespace Statements.Erdos859DivisorSumDensity

def DivisorSumSet (t : ℕ) : Set ℕ :=
  {n : ℕ | ∃ s ⊆ Nat.divisors n, t = ∑ i ∈ s, i}

/-- Natural density, specialized to subsets of `ℕ`. -/
def HasDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((S ∩ Set.Iio N).ncard : ℝ) / N)
    atTop (nhds d)

/-- Erdős Problem 859: the density of integers whose distinct divisors
represent `t` should have a power-of-logarithm asymptotic. -/
abbrev statement : Prop :=
  ∃ c₁ > 0, ∃ c₂ > (0 : ℝ), ∃ d : ℕ → ℝ,
    (∀ t > 0, HasDensity (DivisorSumSet t) (d t)) ∧
      (fun t : ℕ => d t) ~[atTop]
        (fun t => c₁ / Real.log t ^ c₂)

theorem target : statement := sorry

end Statements.Erdos859DivisorSumDensity
