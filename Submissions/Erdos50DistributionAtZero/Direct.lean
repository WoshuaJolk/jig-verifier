import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat

namespace Submissions.Erdos50DistributionAtZero.Direct

open Filter Set Topology

def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((S ∩ Iio N).ncard : ℝ) / N) atTop (𝓝 d)

def isTotientRatioDistribution (f : ℝ → ℝ) : Prop :=
  ∀ c ∈ Icc (0 : ℝ) 1,
    hasNaturalDensity {n : ℕ | (Nat.totient n : ℝ) < c * n} (f c)

theorem proof : ∀ f : ℝ → ℝ, isTotientRatioDistribution f → f 0 = 0 := by
  intro f hf
  have h := hf 0 (by simp)
  have hs : {n : ℕ | (Nat.totient n : ℝ) < (0 : ℝ) * n} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, zero_mul, Set.mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (Nat.cast_nonneg _)
  have hz : hasNaturalDensity
      {n : ℕ | (Nat.totient n : ℝ) < (0 : ℝ) * n} 0 := by
    rw [hs]
    simp [hasNaturalDensity]
  exact tendsto_nhds_unique h hz

end Submissions.Erdos50DistributionAtZero.Direct
