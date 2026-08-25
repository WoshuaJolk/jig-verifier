import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos25EmptyLogDensity

open Filter Finset Real Set
open scoped Topology

def HasLogDensity25 (A : Set ℕ) (d : ℝ) : Prop :=
  open scoped Classical in
  Tendsto (fun n : ℕ => (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / .log n : ℝ)) atTop (𝓝 d)

abbrev statement : Prop := HasLogDensity25 ∅ 0

theorem target : statement := sorry

end Statements.Erdos25EmptyLogDensity
