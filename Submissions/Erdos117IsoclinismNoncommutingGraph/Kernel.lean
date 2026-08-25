import Mathlib.GroupTheory.Commutator.Basic

namespace Submissions.Erdos117IsoclinismNoncommutingGraph.Kernel

open scoped commutatorElement

abbrev CentralCoset (G : Type) [Group G] :=
  G ⧸ Subgroup.center G

def centralCosetMk (G : Type) [Group G] (x : G) : CentralCoset G :=
  QuotientGroup.mk' (Subgroup.center G) x

def derivedComm {G : Type} [Group G] (x y : G) : commutator G :=
  ⟨⁅x, y⁆, by
    exact Subgroup.commutator_mem_commutator (by simp) (by simp)⟩

def CosetsNoncommute (G : Type) [Group G]
    (a b : CentralCoset G) : Prop :=
  ∃ x y : G,
    centralCosetMk G x = a ∧
    centralCosetMk G y = b ∧
    ¬Commute x y

theorem solution :
    ∀ (G H : Type) [Group G] [Group H]
      (alpha : CentralCoset G ≃* CentralCoset H)
      (beta : commutator G ≃* commutator H),
      (∀ (x y : G) (x' y' : H),
        alpha (centralCosetMk G x) = centralCosetMk H x' →
        alpha (centralCosetMk G y) = centralCosetMk H y' →
        beta (derivedComm x y) = derivedComm x' y') →
      ∀ (a b : CentralCoset G),
        CosetsNoncommute G a b ↔
          CosetsNoncommute H (alpha a) (alpha b) := by
  intro G H _ _ alpha beta hmap a b
  constructor
  · rintro ⟨x, y, rfl, rfl, hxy⟩
    obtain ⟨x', hx'⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center H)
        (alpha (centralCosetMk G x))
    obtain ⟨y', hy'⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center H)
        (alpha (centralCosetMk G y))
    refine ⟨x', y', hx', hy', ?_⟩
    intro hcomm
    apply hxy
    rw [← commutatorElement_eq_one_iff_commute]
    have hderived : derivedComm x y = 1 := by
      apply beta.injective
      rw [beta.map_one,
        hmap x y x' y' hx'.symm hy'.symm]
      exact Subtype.ext hcomm.commutator_eq
    exact congrArg Subtype.val hderived
  · rintro ⟨x', y', hx', hy', hx'y'⟩
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center G) a
    obtain ⟨y, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center G) b
    refine ⟨x, y, rfl, rfl, ?_⟩
    intro hcomm
    apply hx'y'
    rw [← commutatorElement_eq_one_iff_commute]
    have hsource : derivedComm x y = 1 :=
      Subtype.ext hcomm.commutator_eq
    have htarget : derivedComm x' y' = 1 := by
      rw [← hmap x y x' y' hx'.symm hy'.symm]
      exact (congrArg beta hsource).trans beta.map_one
    exact congrArg Subtype.val htarget

end Submissions.Erdos117IsoclinismNoncommutingGraph.Kernel
