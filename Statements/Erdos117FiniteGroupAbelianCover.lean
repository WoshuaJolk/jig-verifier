import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Finset.Card

namespace Statements.Erdos117FiniteGroupAbelianCover

def IsAbelianSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

def IsAbelianCover (G : Type) [Group G]
    (C : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ C, IsAbelianSubgroup H) ∧
    ∀ x : G, ∃ H ∈ C, x ∈ H

/-- Every finite group is covered by finitely many cyclic, hence abelian,
subgroups. This establishes the nonempty-cover side of the finite reduction. -/
abbrev statement : Prop :=
  ∀ (G : Type) [Group G] [Fintype G],
    ∃ C : Finset (Subgroup G), IsAbelianCover G C

theorem target : statement := sorry

end Statements.Erdos117FiniteGroupAbelianCover
