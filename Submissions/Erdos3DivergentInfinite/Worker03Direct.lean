import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real

namespace Submissions.Erdos3DivergentInfinite.Worker03Direct

theorem proof :
    ∀ A : Set ℕ,
      (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      Set.Infinite A := by
  intro A hdiv hfinite
  apply hdiv
  letI : Finite A := hfinite.to_subtype
  exact Summable.of_finite

end Submissions.Erdos3DivergentInfinite.Worker03Direct
