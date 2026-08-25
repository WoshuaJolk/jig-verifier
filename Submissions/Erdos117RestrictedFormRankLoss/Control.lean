import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Submissions.Erdos117RestrictedFormRankLoss.Control

open Module

noncomputable def formRank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : ℕ :=
  finrank K (LinearMap.range B)

/-- Must-fail control with an intentional extra false premise. -/
theorem proof :
    False →
      ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
        [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
        (S : Submodule K V),
          formRank B ≤
            formRank (B.restrict S) + 2 * (finrank K V - finrank K S) := by
  intro h
  exact h.elim

end Submissions.Erdos117RestrictedFormRankLoss.Control
