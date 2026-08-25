import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace Submissions.Erdos117AbelianCoverIndependentColors.Kernel

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

noncomputable def colorForSubgroup (G : Type) [Group G]
    [Fintype (CentralCoset G)]
    (H : Subgroup G) : Finset (CentralCoset G) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ h : G, h ∈ H ∧ centralCosetMk G h = q

private theorem commute_left_factors_of_commute_products
    {Q : Type} [Group Q] (a₁ a₂ b₁ b₂ : Q)
    (h₁₂ : Commute b₁ a₂) (h₂₁ : Commute b₂ a₁)
    (hbb : Commute b₁ b₂)
    (hprod : Commute (a₁ * b₁) (a₂ * b₂)) :
    Commute a₁ a₂ := by
  rw [commute_iff_eq]
  apply mul_right_cancel (b := b₁ * b₂)
  calc
    (a₁ * a₂) * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
      simpa only [mul_assoc] using
        (congrArg (fun z : Q => a₁ * z * b₂) h₁₂.eq).symm
    _ = (a₂ * b₂) * (a₁ * b₁) := hprod.eq
    _ = (a₂ * a₁) * (b₂ * b₁) := by
      simpa only [mul_assoc] using
        congrArg (fun z : Q => a₂ * z * b₁) h₂₁.eq
    _ = (a₂ * a₁) * (b₁ * b₂) :=
      congrArg (a₂ * a₁ * ·) hbb.eq.symm

theorem proof :
    ∀ (G : Type) [Group G] [Fintype (CentralCoset G)]
      (A : Finset (Subgroup G)),
        IsAbelianCover G A →
        ∃ C : Finset (Finset (CentralCoset G)),
          (∀ S ∈ C, IndependentColor G S) ∧
          CoversCentralCosets G C ∧
          C.card ≤ A.card := by
  intro G _ _ A hA
  classical
  refine ⟨A.image (colorForSubgroup G), ?_, ?_, Finset.card_image_le⟩
  · intro S hS
    obtain ⟨H, hHA, rfl⟩ := Finset.mem_image.mp hS
    intro q hq r hr hn
    rw [colorForSubgroup, Finset.mem_filter] at hq hr
    obtain ⟨h, hhH, hhq⟩ := hq.2
    obtain ⟨h', hh'H, hh'r⟩ := hr.2
    obtain ⟨x, y, hxq, hyr, hxy⟩ := hn
    have hxh :
        QuotientGroup.mk' (Subgroup.center G) x =
          QuotientGroup.mk' (Subgroup.center G) h :=
      hxq.trans hhq.symm
    have hyh' :
        QuotientGroup.mk' (Subgroup.center G) y =
          QuotientGroup.mk' (Subgroup.center G) h' :=
      hyr.trans hh'r.symm
    obtain ⟨z, hzCenter, hxz⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := Subgroup.center G)).mp hxh
    obtain ⟨w, hwCenter, hyw⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := Subgroup.center G)).mp hyh'
    have hprod : Commute (x * z) (y * w) := by
      rw [hxz, hyw]
      exact hA.1 H hHA h hhH h' hh'H
    have hzy : Commute z y := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hzCenter y).symm
    have hwx : Commute w x := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hwCenter x).symm
    have hzw : Commute z w := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hzCenter w).symm
    exact hxy
      (commute_left_factors_of_commute_products
        x y z w hzy hwx hzw hprod)
  · intro q
    obtain ⟨x, hxq⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center G) q
    obtain ⟨H, hHA, hxH⟩ := hA.2 x
    refine ⟨colorForSubgroup G H,
      Finset.mem_image.mpr ⟨H, hHA, rfl⟩, ?_⟩
    rw [colorForSubgroup, Finset.mem_filter]
    exact ⟨Finset.mem_univ q, x, hxH, hxq⟩

end Submissions.Erdos117AbelianCoverIndependentColors.Kernel
