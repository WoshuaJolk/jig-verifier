import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Submissions.Erdos304OneHalf.Worker04Smoke

def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ,
    s.card = k ∧ (∀ n ∈ s, n > 1) ∧
      (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

theorem proof : 1 ∈ unitFractionExpressible 1 2 := by
  refine ⟨{2}, by norm_num, by norm_num, ?_⟩
  norm_num

end Submissions.Erdos304OneHalf.Worker04Smoke
