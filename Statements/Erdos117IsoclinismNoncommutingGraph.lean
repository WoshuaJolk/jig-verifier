import Mathlib.GroupTheory.Commutator.Basic

namespace Statements.Erdos117IsoclinismNoncommutingGraph

open scoped commutatorElement

abbrev CentralCoset (G : Type) [Group G] :=
  G ⧸ Subgroup.center G

def centralCosetMk (G : Type) [Group G] (x : G) : CentralCoset G :=
  QuotientGroup.mk' (Subgroup.center G) x

def derivedComm {G : Type} [Group G] (x y : G) : commutator G :=
  ⟨⁅x, y⁆, by
    exact Subgroup.commutator_mem_commutator (by simp) (by simp)⟩

/-- The noncommuting relation on central cosets, defined by representatives. -/
def CosetsNoncommute (G : Type) [Group G]
    (a b : CentralCoset G) : Prop :=
  ∃ x y : G,
    centralCosetMk G x = a ∧
    centralCosetMk G y = b ∧
    ¬Commute x y

/-- Core of the graph-invariance part of Lemma 2.1: an isoclinism preserves
and reflects noncommutation of central cosets. -/
abbrev statement : Prop :=
  ∀ (G H : Type) [Group G] [Group H]
    (alpha : CentralCoset G ≃* CentralCoset H)
    (beta : commutator G ≃* commutator H),
    (∀ (x y : G) (x' y' : H),
      alpha (centralCosetMk G x) = centralCosetMk H x' →
      alpha (centralCosetMk G y) = centralCosetMk H y' →
      beta (derivedComm x y) = derivedComm x' y') →
    ∀ (a b : CentralCoset G),
      CosetsNoncommute G a b ↔
        CosetsNoncommute H (alpha a) (alpha b)

theorem target : statement := sorry

end Statements.Erdos117IsoclinismNoncommutingGraph
