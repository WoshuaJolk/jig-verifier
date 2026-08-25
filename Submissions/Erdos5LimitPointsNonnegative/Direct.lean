import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Sequences

namespace Submissions.Erdos5LimitPointsNonnegative.Direct

open Filter Real Set
open scoped Topology

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

noncomputable def normalizedGap (n : ℕ) : ℝ :=
  primeGap n / Real.log n

def limitPointSet : Set ℝ :=
  {x : ℝ | MapClusterPt x atTop normalizedGap}

theorem normalizedGap_nonneg (n : ℕ) : 0 ≤ normalizedGap n :=
  div_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)

theorem proof : limitPointSet ⊆ Set.Ici 0 := by
  intro x hx
  obtain ⟨indices, -, hlimit⟩ := hx.tendsto_subseq
  exact ge_of_tendsto' hlimit fun i => normalizedGap_nonneg (indices i)

end Submissions.Erdos5LimitPointsNonnegative.Direct
