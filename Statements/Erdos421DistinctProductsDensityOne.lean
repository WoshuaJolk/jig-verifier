import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Real.Lemmas

namespace Statements.Erdos421DistinctProductsDensityOne

open Filter Set
open scoped Topology

noncomputable def HasDensityOne (S : Set ℕ) : Prop :=
  Tendsto
    (fun bound : ℕ ↦
      ((S ∩ Iio bound).ncard : ℝ) / bound)
    atTop (𝓝 1)

/-- Erdős Problem 421: a density-one increasing sequence whose nonempty
consecutive interval products are all distinct. -/
abbrev statement : Prop :=
  ∃ d : ℕ → ℕ, StrictMono d ∧ 1 ≤ d 0 ∧ HasDensityOne (range d) ∧
    {(u, v) : ℕ × ℕ | u ≤ v}.InjOn
      (fun uv ↦ ∏ i ∈ Finset.Icc uv.1 uv.2, d i)

theorem target : statement := sorry

end Statements.Erdos421DistinctProductsDensityOne
