import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos770PrimeValueDensities

open Set ENat Filter Topology

noncomputable def h (n : ℕ) : ℕ∞ :=
  sInf {m | 2 < m ∧
    ((Finset.Icc 2 m.toNat).image fun i => i ^ n - 1).gcd id = 1}

noncomputable abbrev partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=
  ((S ∩ Iio b).ncard : ℝ) / ((Iio b).ncard : ℝ)

def HasDensity (S : Set ℕ) (a : ℝ) : Prop :=
  Tendsto (fun b : ℕ => partialDensity S b) atTop (𝓝 a)

/-- Erdős Problem 770(i): every prime value of `h` has a natural density. -/
abbrev statement : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ℝ, HasDensity {n | h n = p} a

theorem target : statement := sorry

end Statements.Erdos770PrimeValueDensities
