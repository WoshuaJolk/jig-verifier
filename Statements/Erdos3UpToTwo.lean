import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Statements.Erdos3UpToTwo

/-- The Erdős reciprocal-sum conjecture holds for progression lengths at most two. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∀ k : ℕ, k ≤ 2 →
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

theorem target : statement := sorry

end Statements.Erdos3UpToTwo
