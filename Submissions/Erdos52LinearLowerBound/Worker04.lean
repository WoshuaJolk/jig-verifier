import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Pointwise

namespace Submissions.Erdos52LinearLowerBound.Worker04

theorem proof :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) := by
  refine ⟨1, by norm_num, ?_⟩
  intro A
  norm_num
  exact Or.inl (Finset.card_le_card_add_self (s := A))

end Submissions.Erdos52LinearLowerBound.Worker04
