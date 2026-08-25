import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Subgroup.Basic

namespace Submissions.Erdos117DistinctCosetProductCardinality.Kernel

theorem proof :
    ∀ (G : Type) [Group G] [DecidableEq G]
      (A : Subgroup G) (T D : Finset G),
        (∀ d ∈ D, d ∈ A) →
        (∀ a ∈ T, ∀ a' ∈ T, a ≠ a' → a⁻¹ * a' ∉ A) →
        ((T.product D).image (fun q : G × G ↦ q.1 * q.2)).card =
          T.card * D.card := by
  intro G _ _ A T D hD hT
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_product T D
  · rintro ⟨a, d⟩ had ⟨a', d'⟩ ha'd had_eq
    have had_parts : a ∈ T ∧ d ∈ D := Finset.mem_product.mp had
    have ha'd_parts : a' ∈ T ∧ d' ∈ D := Finset.mem_product.mp ha'd
    change a * d = a' * d' at had_eq
    have hcoset : a⁻¹ * a' = d * d'⁻¹ := by
      calc
        a⁻¹ * a' = a⁻¹ * (a' * d') * d'⁻¹ := by simp [mul_assoc]
        _ = a⁻¹ * (a * d) * d'⁻¹ := by rw [← had_eq]
        _ = d * d'⁻¹ := by simp
    have haa' : a = a' := by
      by_contra hne
      exact hT a had_parts.1 a' ha'd_parts.1 hne
        (hcoset ▸ A.mul_mem (hD d had_parts.2)
          (A.inv_mem (hD d' ha'd_parts.2)))
    subst a'
    have hdd' : d = d' := mul_left_cancel had_eq
    subst d'
    rfl

end Submissions.Erdos117DistinctCosetProductCardinality.Kernel
