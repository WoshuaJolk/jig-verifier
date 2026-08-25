import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace Statements.Erdos117AbelianCoverIndependentColors

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

/-- The cover-to-color direction in arXiv:2608.20507v1, Lemma 2.1, for a
finite central quotient: an abelian-subgroup cover gives a cover of the
central-coset noncommuting graph by independent color classes, with no more
classes. -/
abbrev statement : Prop :=
  ∀ (G : Type) [Group G] [Fintype (CentralCoset G)]
    (A : Finset (Subgroup G)),
      IsAbelianCover G A →
      ∃ C : Finset (Finset (CentralCoset G)),
        (∀ S ∈ C, IndependentColor G S) ∧
        CoversCentralCosets G C ∧
        C.card ≤ A.card

theorem target : statement := sorry

end Statements.Erdos117AbelianCoverIndependentColors
