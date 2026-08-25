import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

namespace Submissions.Erdos770PrimeTwoDensity.Direct

open Set ENat Filter Topology

noncomputable def h (n : ℕ) : ℕ∞ :=
  sInf {m | 2 < m ∧
    ((Finset.Icc 2 m.toNat).image fun i => i ^ n - 1).gcd id = 1}

noncomputable abbrev partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=
  ((S ∩ Iio b).ncard : ℝ) / ((Iio b).ncard : ℝ)

def HasDensity (S : Set ℕ) (a : ℝ) : Prop :=
  Tendsto (fun b : ℕ => partialDensity S b) atTop (𝓝 a)

theorem h_three_le (n : ℕ) : (3 : ℕ∞) ≤ h n := by
  apply le_sInf
  intro m hm
  change (3 : ℕ∞) ≤ m
  exact ENat.natCast_add_one_le_iff.mpr hm.1

theorem proof : HasDensity {n : ℕ | h n = 2} 0 := by
  have hs : {n : ℕ | h n = 2} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hn => by
      have hlower := h_three_le n
      rw [hn] at hlower
      norm_num at hlower
  rw [hs]
  simp [HasDensity, partialDensity]

end Submissions.Erdos770PrimeTwoDensity.Direct
