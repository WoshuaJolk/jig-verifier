import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Instances.Nat

open Nat Filter Finset
open scoped ArithmeticFunction.omega

namespace Submissions.Erdos891ZeroFactorBoundary.Worker03SelfWitness

theorem proof :
    ∀ᶠ n : ℕ in atTop,
      ∃ m ∈ Ico n (n + 1), 0 < ω m := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  refine ⟨n, ?_, ?_⟩
  · simp
  · exact ArithmeticFunction.cardDistinctFactors_pos.mpr hn

end Submissions.Erdos891ZeroFactorBoundary.Worker03SelfWitness
