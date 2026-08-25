import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace Statements.Erdos117IndependentColorsAbelianCover

abbrev CentralCoset (G : Type) [Group G] :=
  G ⧸ Subgroup.center G

def centralCosetMk (G : Type) [Group G] (x : G) : CentralCoset G :=
  QuotientGroup.mk' (Subgroup.center G) x

def CosetsNoncommute (G : Type) [Group G]
    (a b : CentralCoset G) : Prop :=
  ∃ x y : G,
    centralCosetMk G x = a ∧
    centralCosetMk G y = b ∧
    ¬Commute x y

def IndependentColor (G : Type) [Group G]
    (S : Finset (CentralCoset G)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬CosetsNoncommute G a b

def CoversCentralCosets (G : Type) [Group G]
    (C : Finset (Finset (CentralCoset G))) : Prop :=
  ∀ q : CentralCoset G, ∃ S ∈ C, q ∈ S

def IsAbelianSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

def IsAbelianCover (G : Type) [Group G]
    (A : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ A, IsAbelianSubgroup H) ∧
    ∀ x : G, ∃ H ∈ A, x ∈ H

/-- The coloring-to-cover direction in arXiv:2608.20507v1, Lemma 2.1:
each independent color class generates an abelian subgroup, and a finite
color cover of the central quotient yields an abelian-subgroup cover with no
more members. -/
abbrev statement : Prop :=
  ∀ (G : Type) [Group G]
    (C : Finset (Finset (CentralCoset G))),
      (∀ S ∈ C, IndependentColor G S) →
      CoversCentralCosets G C →
      ∃ A : Finset (Subgroup G),
        IsAbelianCover G A ∧ A.card ≤ C.card

theorem target : statement := sorry

end Statements.Erdos117IndependentColorsAbelianCover
