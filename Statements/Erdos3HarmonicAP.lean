import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Statements.Erdos3HarmonicAP

/-- Erdős Problem 3: a set of natural numbers with divergent reciprocal sum
contains arithmetic progressions of every finite length. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

theorem target : statement := sorry

end Statements.Erdos3HarmonicAP
