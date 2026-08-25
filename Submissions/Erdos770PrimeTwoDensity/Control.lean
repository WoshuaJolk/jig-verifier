import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Instances.Nat

namespace Submissions.Erdos770PrimeTwoDensity.Control

open Set ENat Filter Topology

noncomputable def h (n : ℕ) : ℕ∞ :=
  sInf {m | 2 < m ∧
    ((Finset.Icc 2 m.toNat).image fun i => i ^ n - 1).gcd id = 1}

noncomputable abbrev partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=
  ((S ∩ Iio b).ncard : ℝ) / ((Iio b).ncard : ℝ)

def HasDensity (S : Set ℕ) (a : ℝ) : Prop :=
  Tendsto (fun b : ℕ => partialDensity S b) atTop (𝓝 a)

abbrev claimedStatement : Prop := HasDensity {n : ℕ | h n = 2} 0

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos770PrimeTwoDensity.Control
