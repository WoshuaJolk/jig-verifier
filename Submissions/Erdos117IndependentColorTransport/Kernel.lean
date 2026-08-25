import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace Submissions.Erdos117IndependentColorTransport.Kernel

def IsIndependentCover {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (C : Finset (Finset α)) : Prop :=
  (∀ x : α, ∃ S ∈ C, x ∈ S) ∧
  (∀ S ∈ C, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y)

def transportColors {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (C : Finset (Finset α)) : Finset (Finset β) :=
  C.image (fun S ↦ S.image e)

theorem proof :
    ∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
      (R : α → α → Prop) (Q : β → β → Prop) (e : α ≃ β),
      (∀ x y, R x y ↔ Q (e x) (e y)) →
      ∀ C : Finset (Finset α),
        IsIndependentCover R C →
        IsIndependentCover Q (transportColors e C) ∧
          (transportColors e C).card = C.card := by
  intro α β _ _ R Q e hrel C hC
  constructor
  · constructor
    · intro y
      obtain ⟨S, hSC, hyS⟩ := hC.1 (e.symm y)
      refine ⟨S.image e, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨S, hSC, rfl⟩
      · exact Finset.mem_image.mpr
          ⟨e.symm y, hyS, e.apply_symm_apply y⟩
    · intro T hTC x hxT y hyT hxy
      obtain ⟨S, hSC, rfl⟩ := Finset.mem_image.mp hTC
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hxT
      obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hyT
      have hxy₀ : x₀ ≠ y₀ := fun h ↦ hxy (congrArg e h)
      intro hQ
      exact hC.2 S hSC x₀ hx₀ y₀ hy₀ hxy₀ ((hrel x₀ y₀).mpr hQ)
  · unfold transportColors
    rw [Finset.card_image_of_injective]
    intro S T hST
    ext x
    have h := congrArg (fun U : Finset β ↦ e x ∈ U) hST
    simpa using h

end Submissions.Erdos117IndependentColorTransport.Kernel
