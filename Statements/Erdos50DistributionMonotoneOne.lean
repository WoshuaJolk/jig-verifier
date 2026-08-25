import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat

namespace Statements.Erdos50DistributionMonotoneOne

open Filter Set Topology

def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((S ∩ Iio N).ncard : ℝ) / N) atTop (𝓝 d)

def isTotientRatioDistribution (f : ℝ → ℝ) : Prop :=
  ∀ c ∈ Icc (0 : ℝ) 1,
    hasNaturalDensity {n : ℕ | (Nat.totient n : ℝ) < c * n} (f c)

/-- Every totient-ratio distribution is monotone on its natural domain and equals one at one. -/
abbrev statement : Prop :=
  ∀ f : ℝ → ℝ, isTotientRatioDistribution f →
    MonotoneOn f (Icc (0 : ℝ) 1) ∧ f 1 = 1

theorem target : statement := sorry

end Statements.Erdos50DistributionMonotoneOne
