import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos234ZeroThresholdDensity.Direct

open Filter Real Set
open scoped NNReal Topology

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

noncomputable abbrev partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=
  (S ∩ Set.Iio b).ncard / (Set.Iio b).ncard

def HasDensity (S : Set ℕ) (α : ℝ) : Prop :=
  Tendsto (fun b : ℕ => partialDensity S b) atTop (𝓝 α)

theorem threshold_zero_empty :
    {n : ℕ | (primeGap n : ℝ) / Real.log n < (0 : ℝ≥0)} = ∅ := by
  ext n
  change (primeGap n : ℝ) / Real.log n < 0 ↔ False
  rw [iff_false]
  apply not_lt_of_ge
  apply div_nonneg (Nat.cast_nonneg _)
  cases n with
  | zero => simp
  | succ n =>
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)

theorem proof :
    HasDensity
      {n : ℕ | (primeGap n : ℝ) / Real.log n < (0 : ℝ≥0)}
      0 := by
  rw [threshold_zero_empty]
  simpa [HasDensity, partialDensity] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end Submissions.Erdos234ZeroThresholdDensity.Direct
