import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Statements.Erdos3DivergentInfinite

/-- A set of natural numbers whose reciprocal sum diverges is infinite. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    Set.Infinite A

theorem target : statement := sorry

end Statements.Erdos3DivergentInfinite
