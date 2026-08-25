import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos218PrimeGapComparisonDensity

open Filter Set Topology

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((S ∩ Iio N).ncard : ℝ) / N) atTop (𝓝 d)

/-- Erdős Problem 218, comparison-density question: each direction of
comparison between consecutive prime gaps has natural density one half. -/
abbrev statement : Prop :=
  hasNaturalDensity {n | primeGap n ≤ primeGap (n + 1)} (1 / 2) ∧
  hasNaturalDensity {n | primeGap (n + 1) ≤ primeGap n} (1 / 2)

theorem target : statement := sorry

end Statements.Erdos218PrimeGapComparisonDensity
