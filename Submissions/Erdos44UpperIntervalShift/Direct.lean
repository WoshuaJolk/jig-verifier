import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44UpperIntervalShift.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def CrossUnique (A C : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ c₁ ∈ C, ∀ c₂ ∈ C,
    a₁ + c₁ = a₂ + c₂ → a₁ = a₂ ∧ c₁ = c₂

private theorem shifted_union_sidon
    (N R L t : ℕ) (hOld : 2 * N < t + R + 1)
    (hMixed : N + L < t + 2 * R)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 N)
    (hA : IsSidon (A : Set ℕ))
    (C : Finset ℕ) (hCsub : C ⊆ Finset.Icc R L)
    (hC : IsSidon (C : Set ℕ)) (hcross : CrossUnique A C) :
    IsSidon ((A ∪ C.image (fun c => t + c) : Finset ℕ) : Set ℕ) := by
  let B := C.image (fun c => t + c)
  have oldBounds : ∀ ⦃a : ℕ⦄, a ∈ A → 1 ≤ a ∧ a ≤ N := by
    intro a ha
    exact Finset.mem_Icc.mp (hAsub ha)
  have newBounds : ∀ ⦃c : ℕ⦄, c ∈ C → R ≤ c ∧ c ≤ L := by
    intro c hc
    exact Finset.mem_Icc.mp (hCsub hc)
  have classify : ∀ ⦃z : ℕ⦄, z ∈ (A ∪ B : Finset ℕ) →
      z ∈ A ∨ ∃ c ∈ C, z = t + c := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Or.inl hz
    · rcases Finset.mem_image.mp hz with ⟨c, hc, rfl⟩
      exact Or.inr ⟨c, hc, rfl⟩
  change IsSidon ((A ∪ B : Finset ℕ) : Set ℕ)
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  rcases classify hi₁ with hi₁ | ⟨c₁, hc₁, rfl⟩ <;>
    rcases classify hj₁ with hj₁ | ⟨d₁, hd₁, rfl⟩ <;>
      rcases classify hi₂ with hi₂ | ⟨c₂, hc₂, rfl⟩ <;>
        rcases classify hj₂ with hj₂ | ⟨d₂, hd₂, rfl⟩
  all_goals
    try have hi₁b := oldBounds hi₁
    try have hj₁b := oldBounds hj₁
    try have hi₂b := oldBounds hi₂
    try have hj₂b := oldBounds hj₂
    try have hc₁b := newBounds hc₁
    try have hd₁b := newBounds hd₁
    try have hc₂b := newBounds hc₂
    try have hd₂b := newBounds hd₂
  · exact hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  · omega
  · omega
  ·
    have hu := hcross i₁ hi₁ j₁ hj₁ c₂ hc₂ d₂ hd₂ (by omega)
    left
    exact ⟨hu.1, by omega⟩
  · omega
  · omega
  ·
    have hu := hcross i₁ hi₁ j₂ hj₂ c₂ hc₂ d₁ hd₁ (by omega)
    right
    exact ⟨hu.1, by omega⟩
  · omega
  · omega
  ·
    have hu := hcross i₂ hi₂ j₁ hj₁ c₁ hc₁ d₂ hd₂ (by omega)
    right
    exact ⟨by omega, hu.1⟩
  · omega
  · omega
  ·
    have hu := hcross i₂ hi₂ j₂ hj₂ c₁ hc₁ d₁ hd₁ (by omega)
    left
    exact ⟨by omega, hu.1⟩
  · omega
  · omega
  ·
    have hs : c₁ + c₂ = d₁ + d₂ := by omega
    rcases hC c₁ hc₁ d₁ hd₁ c₂ hc₂ d₂ hd₂ hs with h | h
    · left
      exact ⟨by omega, by omega⟩
    · right
      exact ⟨by omega, by omega⟩

theorem proof :
    ∀ (N R L t : ℕ) (A C : Finset ℕ), 1 ≤ N → R ≤ L →
      2 * N < t + R + 1 → N + L < t + 2 * R →
      A ⊆ Finset.Icc 1 N → C ⊆ Finset.Icc R L →
      IsSidon (A : Set ℕ) → IsSidon (C : Set ℕ) → CrossUnique A C →
          let B := C.image (fun c => t + c)
          B ⊆ Finset.Icc (N + 1) (t + L) ∧
            B.card = C.card ∧
              (A ∪ B).card = A.card + C.card ∧
                IsSidon (A ∪ B : Set ℕ) := by
  intro N R L t A C hN hRL hOld hMixed hAsub hCsub hA hC hcross
  let B := C.image (fun c => t + c)
  have hBsub : B ⊆ Finset.Icc (N + 1) (t + L) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨c, hc, rfl⟩
    have cb := Finset.mem_Icc.mp (hCsub hc)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard : B.card = C.card := by
    apply Finset.card_image_of_injective
    intro c d h
    change t + c = t + d at h
    omega
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr fun a haA haB => by
    have aN := (Finset.mem_Icc.mp (hAsub haA)).2
    have aLower := (Finset.mem_Icc.mp (hBsub haB)).1
    omega
  refine ⟨hBsub, hcard, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hcard]
  · simpa only [Finset.coe_union] using
      shifted_union_sidon N R L t hOld hMixed A hAsub hA C hCsub hC hcross

end Submissions.Erdos44UpperIntervalShift.Direct
