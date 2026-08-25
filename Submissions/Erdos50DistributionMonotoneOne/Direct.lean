import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat

namespace Submissions.Erdos50DistributionMonotoneOne.Direct

open Filter Set Topology

def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((S ∩ Iio N).ncard : ℝ) / N) atTop (𝓝 d)

def isTotientRatioDistribution (f : ℝ → ℝ) : Prop :=
  ∀ c ∈ Icc (0 : ℝ) 1,
    hasNaturalDensity {n : ℕ | (Nat.totient n : ℝ) < c * n} (f c)

private theorem distribution_monotone
    (f : ℝ → ℝ) (hf : isTotientRatioDistribution f) :
    MonotoneOn f (Icc 0 1) := by
  intro a ha b hb hab
  apply le_of_tendsto_of_tendsto (hf a ha) (hf b hb)
  filter_upwards [] with N
  apply div_le_div_of_nonneg_right
  · norm_cast
    apply Set.ncard_le_ncard ?_ ((Set.finite_Iio N).inter_of_right _)
    intro n hn
    refine ⟨?_, hn.2⟩
    exact lt_of_lt_of_le hn.1 (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n))
  · exact Nat.cast_nonneg N

private theorem distribution_at_one
    (f : ℝ → ℝ) (hf : isTotientRatioDistribution f) : f 1 = 1 := by
  have h := hf 1 (by norm_num)
  have hs : {n : ℕ | (Nat.totient n : ℝ) < (1 : ℝ) * n} = Ici 2 := by
    ext n
    simp only [Set.mem_ofPred_eq, one_mul, Set.mem_Ici]
    constructor
    · intro hn
      have hn' : Nat.totient n < n := by exact_mod_cast hn
      by_contra hnot
      have hnle : n ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · norm_num at hn'
      · have : n = 1 := by omega
        subst n
        norm_num at hn'
    · intro hn
      exact_mod_cast Nat.totient_lt n (by omega)
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun N : ℕ => (2 : ℝ) * ((N : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have hlim : Tendsto (fun N : ℕ => ((N - 2 : ℕ) : ℝ) / N) atTop (𝓝 1) := by
    have hbase : Tendsto (fun N : ℕ => (1 : ℝ) - 2 * ((N : ℝ))⁻¹)
        atTop (𝓝 (1 : ℝ)) := by
      convert tendsto_const_nhds.sub htwo using 1 <;> norm_num
    apply hbase.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Nat.cast_sub hN]
    field_simp [Nat.cast_ne_zero.mpr (by omega : N ≠ 0)]
    norm_num
  have hone : hasNaturalDensity
      {n : ℕ | (Nat.totient n : ℝ) < (1 : ℝ) * n} 1 := by
    rw [hs]
    simpa [hasNaturalDensity, Ici_inter_Iio] using hlim
  exact tendsto_nhds_unique h hone

theorem proof :
    ∀ f : ℝ → ℝ, isTotientRatioDistribution f →
      MonotoneOn f (Icc (0 : ℝ) 1) ∧ f 1 = 1 := by
  intro f hf
  exact ⟨distribution_monotone f hf, distribution_at_one f hf⟩

end Submissions.Erdos50DistributionMonotoneOne.Direct
