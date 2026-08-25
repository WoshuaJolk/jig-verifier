import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Statements.Erdos117RestrictedFormRankLoss

open Module

/-- Rank of a finite-dimensional bilinear form as a linear map into the dual. -/
noncomputable def formRank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : ℕ :=
  finrank K (LinearMap.range B)

/-- The restricted-form rank-loss estimate used in arXiv:2608.20507v1,
Lemma 5.7, TeX line 473. -/
abbrev statement : Prop :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (S : Submodule K V),
      formRank B ≤
        formRank (B.restrict S) + 2 * (finrank K V - finrank K S)

theorem target : statement := sorry

end Statements.Erdos117RestrictedFormRankLoss
