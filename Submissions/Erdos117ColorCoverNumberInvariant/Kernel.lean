import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos117ColorCoverNumberInvariant.Kernel

def IsIndependentCover {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (C : Finset (Finset α)) : Prop :=
  (∀ x : α, ∃ S ∈ C, x ∈ S) ∧
  (∀ S ∈ C, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y)

noncomputable def colorCoverNumber {α : Type*} [DecidableEq α]
    (R : α → α → Prop) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Finset α),
    C.card = k ∧ IsIndependentCover R C}

private def transportColors
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (C : Finset (Finset α)) : Finset (Finset β) :=
  C.image (fun S ↦ S.image e)

private theorem transport
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → α → Prop) (Q : β → β → Prop) (e : α ≃ β)
    (hrel : ∀ x y, R x y ↔ Q (e x) (e y))
    (C : Finset (Finset α)) (hC : IsIndependentCover R C) :
    IsIndependentCover Q (transportColors e C) ∧
      (transportColors e C).card = C.card := by
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

theorem proof :
    ∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
      (R : α → α → Prop) (Q : β → β → Prop) (e : α ≃ β),
      (∀ x y, R x y ↔ Q (e x) (e y)) →
      (∃ C : Finset (Finset α), IsIndependentCover R C) →
      colorCoverNumber R = colorCoverNumber Q := by
  intro α β _ _ R Q e hrel hex
  let A : Set ℕ := {k | ∃ C : Finset (Finset α),
    C.card = k ∧ IsIndependentCover R C}
  let B : Set ℕ := {k | ∃ C : Finset (Finset β),
    C.card = k ∧ IsIndependentCover Q C}
  have hA : A.Nonempty := by
    obtain ⟨C, hC⟩ := hex
    exact ⟨C.card, C, rfl, hC⟩
  have hAB : ∀ a ∈ A, ∃ b ∈ B, b ≤ a := by
    rintro a ⟨C, rfl, hC⟩
    obtain ⟨hTC, hcard⟩ := transport R Q e hrel C hC
    exact ⟨(transportColors e C).card,
      ⟨transportColors e C, rfl, hTC⟩, hcard.le⟩
  have hrelSymm :
      ∀ x y, Q x y ↔ R (e.symm x) (e.symm y) := by
    intro x y
    simpa using (hrel (e.symm x) (e.symm y)).symm
  have hB : B.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb, _⟩ := hAB a ha
    exact ⟨b, hb⟩
  have hBA : ∀ b ∈ B, ∃ a ∈ A, a ≤ b := by
    rintro b ⟨C, rfl, hC⟩
    obtain ⟨hTC, hcard⟩ :=
      transport Q R e.symm hrelSymm C hC
    exact ⟨(transportColors e.symm C).card,
      ⟨transportColors e.symm C, rfl, hTC⟩, hcard.le⟩
  change sInf A = sInf B
  apply le_antisymm
  · obtain ⟨a, ha, hab⟩ := hBA (sInf B) (Nat.sInf_mem hB)
    exact (Nat.sInf_le ha).trans hab
  · obtain ⟨b, hb, hba⟩ := hAB (sInf A) (Nat.sInf_mem hA)
    exact (Nat.sInf_le hb).trans hba

end Submissions.Erdos117ColorCoverNumberInvariant.Kernel
