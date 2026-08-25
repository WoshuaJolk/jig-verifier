import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat

namespace Statements.Erdos50NoPositiveDerivative

open Filter Set Topology

/-- Natural density, specialized to subsets of the natural numbers. -/
def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((S ∩ Iio N).ncard : ℝ) / N) atTop (𝓝 d)

/-- `f(c)` is the asymptotic density of the integers with
`Nat.totient n / n < c`. -/
def isTotientRatioDistribution (f : ℝ → ℝ) : Prop :=
  ∀ c ∈ Icc (0 : ℝ) 1,
    hasNaturalDensity {n : ℕ | (Nat.totient n : ℝ) < c * n} (f c)

/-- Erdős Problem 50: the totient-ratio distribution has no finite
positive derivative on its natural domain. -/
abbrev statement : Prop :=
  ∀ f : ℝ → ℝ, isTotientRatioDistribution f →
    ¬∃ x ∈ Icc (0 : ℝ) 1, ∃ y > 0,
      HasDerivWithinAt f y (Icc 0 1) x

theorem target : statement := sorry

end Statements.Erdos50NoPositiveDerivative
