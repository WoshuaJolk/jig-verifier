import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

open Filter

namespace Statements.Erdos955ProperDivisorPreimages

def s (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d

def HasDensity (A : Set ℕ) (density : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (((A ∩ Set.Iio N).ncard : ℕ) : ℝ) / N)
    atTop (nhds density)

/-- Erdős Problem 955 (the EGPS conjecture): preimages under the
sum-of-proper-divisors map preserve asymptotic density zero. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, HasDensity A 0 →
    HasDensity {n : ℕ | s n ∈ A} 0

theorem target : statement := sorry

end Statements.Erdos955ProperDivisorPreimages
