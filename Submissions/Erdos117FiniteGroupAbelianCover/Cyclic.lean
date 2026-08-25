import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Finset.Card

open scoped IsMulCommutative

namespace Submissions.Erdos117FiniteGroupAbelianCover.Cyclic

def IsAbelianSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

def IsAbelianCover (G : Type) [Group G]
    (C : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ C, IsAbelianSubgroup H) ∧
    ∀ x : G, ∃ H ∈ C, x ∈ H

theorem proof :
    ∀ (G : Type) [Group G] [Fintype G],
      ∃ C : Finset (Subgroup G), IsAbelianCover G C := by
  intro G _ _
  classical
  refine ⟨Finset.univ.image Subgroup.zpowers, ?_⟩
  constructor
  · intro H hH
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hH
    intro x hx y hy
    exact congrArg Subtype.val
      (mul_comm (⟨x, hx⟩ : Subgroup.zpowers g)
        (⟨y, hy⟩ : Subgroup.zpowers g))
  · intro x
    refine ⟨Subgroup.zpowers x, ?_, Subgroup.mem_zpowers x⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

end Submissions.Erdos117FiniteGroupAbelianCover.Cyclic
