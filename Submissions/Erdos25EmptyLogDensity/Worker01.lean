import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos25EmptyLogDensity.Worker01

open Filter Finset Real Set
open scoped Topology

def HasLogDensity25 (A : Set ℕ) (d : ℝ) : Prop :=
  open scoped Classical in
  Tendsto (fun n : ℕ => (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / .log n : ℝ)) atTop (𝓝 d)

theorem proof : HasLogDensity25 ∅ 0 := by
  simpa [HasLogDensity25] using tendsto_const_nhds

end Submissions.Erdos25EmptyLogDensity.Worker01
