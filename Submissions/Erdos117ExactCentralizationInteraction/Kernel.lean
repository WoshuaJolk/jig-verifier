import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commute.Hom

namespace Submissions.Erdos117ExactCentralizationInteraction.Kernel

open scoped commutatorElement

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
    ∀ (G : Type) [Group G] (K : Subgroup G) [K.Normal]
      (a₁ a₂ b₁ b₂ : G),
        Commute b₁ a₂ →
        Commute b₂ a₁ →
        ⁅b₁, b₂⁆ ∈ K →
        ⁅a₁, a₂⁆ ∉ K →
        ¬Commute (a₁ * b₁) (a₂ * b₂) := by
  intro G _ K _ a₁ a₂ b₁ b₂ h₁₂ h₂₁ hb ha hprod
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hbbQ : Commute (q b₁) (q b₂) := by
    rw [← commutatorElement_eq_one_iff_commute,
      ← map_commutatorElement]
    change (↑⁅b₁, b₂⁆ : G ⧸ K) = 1
    rwa [QuotientGroup.eq_one_iff]
  have haaQ : Commute (q a₁) (q a₂) :=
    commute_left_factors_of_commute_products
      (q a₁) (q a₂) (q b₁) (q b₂)
      (h₁₂.map q) (h₂₁.map q) hbbQ (hprod.map q)
  apply ha
  rw [← QuotientGroup.eq_one_iff]
  change q ⁅a₁, a₂⁆ = 1
  rw [map_commutatorElement]
  exact haaQ.commutator_eq

end Submissions.Erdos117ExactCentralizationInteraction.Kernel
