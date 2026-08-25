import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos117FiniteCoverNumberInvariant

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

def IsAbelianSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

def IsAbelianCover (G : Type) [Group G]
    (A : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ A, IsAbelianSubgroup H) ∧
  ∀ x : G, ∃ H ∈ A, x ∈ H

noncomputable def abelianCoverNumber (G : Type) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ A : Finset (Subgroup G),
    A.card = k ∧ IsAbelianCover G A}

/-- Exact finite/combinatorial cover-number assembly in
arXiv:2608.20507v1, Lemma 2.1, after central-coset graph invariance is supplied. -/
abbrev statement : Prop :=
  ∀ (G H : Type) [Group G] [Group H]
    [Fintype (CentralCoset G)] [Fintype (CentralCoset H)]
    (e : CentralCoset G ≃ CentralCoset H),
    (∀ a b, CosetsNoncommute G a b ↔
      CosetsNoncommute H (e a) (e b)) →
    abelianCoverNumber G = abelianCoverNumber H

theorem target : statement := sorry

end Statements.Erdos117FiniteCoverNumberInvariant
