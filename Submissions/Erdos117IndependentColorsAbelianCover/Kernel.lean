import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer

open scoped IsMulCommutative

namespace Submissions.Erdos117IndependentColorsAbelianCover.Kernel

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

def subgroupForColor (G : Type) [Group G]
    (S : Finset (CentralCoset G)) : Subgroup G :=
  Subgroup.closure {x : G | centralCosetMk G x ∈ S}

theorem proof :
    ∀ (G : Type) [Group G]
      (C : Finset (Finset (CentralCoset G))),
        (∀ S ∈ C, IndependentColor G S) →
        CoversCentralCosets G C →
        ∃ A : Finset (Subgroup G),
          IsAbelianCover G A ∧ A.card ≤ C.card := by
  intro G _ C hIndependent hCover
  classical
  refine ⟨C.image (subgroupForColor G), ?_, Finset.card_image_le⟩
  constructor
  · intro H hH
    obtain ⟨S, hSC, rfl⟩ := Finset.mem_image.mp hH
    have hcomm :
        ∀ x ∈ {x : G | centralCosetMk G x ∈ S},
          ∀ y ∈ {y : G | centralCosetMk G y ∈ S},
            x * y = y * x := by
      intro x hx y hy
      by_contra hxy
      exact hIndependent S hSC
        (centralCosetMk G x) hx
        (centralCosetMk G y) hy
        ⟨x, y, rfl, rfl, hxy⟩
    letI : IsMulCommutative (subgroupForColor G S) :=
      Subgroup.isMulCommutative_closure hcomm
    intro x hx y hy
    exact congrArg Subtype.val
      (mul_comm
        (⟨x, hx⟩ : subgroupForColor G S)
        (⟨y, hy⟩ : subgroupForColor G S))
  · intro x
    obtain ⟨S, hSC, hxS⟩ := hCover (centralCosetMk G x)
    refine ⟨subgroupForColor G S, Finset.mem_image.mpr ⟨S, hSC, rfl⟩, ?_⟩
    exact Subgroup.subset_closure hxS

end Submissions.Erdos117IndependentColorsAbelianCover.Kernel
