import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos117AbelianColorCoverNumber.Control

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

def IsColorCover (G : Type) [Group G]
    (C : Finset (Finset (CentralCoset G))) : Prop :=
  (∀ S ∈ C, IndependentColor G S) ∧
  ∀ q : CentralCoset G, ∃ S ∈ C, q ∈ S

def IsAbelianSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

def IsAbelianCover (G : Type) [Group G]
    (A : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ A, IsAbelianSubgroup H) ∧
  ∀ x : G, ∃ H ∈ A, x ∈ H

noncomputable def abelianCoverNumber (G : Type) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ A : Finset (Subgroup G),
    A.card = k ∧ IsAbelianCover G A}

noncomputable def colorCoverNumber (G : Type) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Finset (CentralCoset G)),
    C.card = k ∧ IsColorCover G C}

/-- For a finite central quotient, the least abelian-subgroup-cover
cardinality equals the least independent central-coset color-cover
cardinality. -/
abbrev statement : Prop :=
  ∀ (G : Type) [Group G] [Fintype (CentralCoset G)],
    abelianCoverNumber G = colorCoverNumber G

theorem proof : False → statement := by
  intro h
  exact h.elim

end Submissions.Erdos117AbelianColorCoverNumber.Control
