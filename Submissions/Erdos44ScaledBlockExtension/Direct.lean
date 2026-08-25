import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44ScaledBlockExtension.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

private lemma mixed_unique
    (N a₁ a₂ c₁ c₂ : ℕ) (hN : 1 ≤ N)
    (ha₁ : 1 ≤ a₁) (ha₁N : a₁ ≤ N)
    (ha₂ : 1 ≤ a₂) (ha₂N : a₂ ≤ N)
    (h : a₁ + (2 * N) * c₁ = a₂ + (2 * N) * c₂) :
    a₁ = a₂ ∧ c₁ = c₂ := by
  let q := 2 * N
  have ha₁q : a₁ < q := by dsimp [q]; omega
  have ha₂q : a₂ < q := by dsimp [q]; omega
  change a₁ + q * c₁ = a₂ + q * c₂ at h
  have hm := congrArg (fun z : ℕ => z % q) h
  have haa : a₁ = a₂ := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ha₁q,
      Nat.mod_eq_of_lt ha₂q] using hm
  subst a₂
  have hp : q * c₁ = q * c₂ := by omega
  exact ⟨rfl, Nat.mul_left_cancel (by dsimp [q]; omega) hp⟩

private lemma old_old_ne_old_block
    (N a b d c : ℕ) (hN : 1 ≤ N)
    (ha : a ≤ N) (hb : b ≤ N) (hd : 1 ≤ d) (hc : 1 ≤ c) :
    a + b ≠ d + (2 * N) * c := by
  have hscale : 2 * N ≤ (2 * N) * c := by
    simpa using Nat.mul_le_mul_left (2 * N) hc
  omega

private lemma old_old_ne_block_block
    (N a b c d : ℕ) (hN : 1 ≤ N)
    (ha : a ≤ N) (hb : b ≤ N) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    a + b ≠ (2 * N) * c + (2 * N) * d := by
  have hcscale : 2 * N ≤ (2 * N) * c := by
    simpa using Nat.mul_le_mul_left (2 * N) hc
  have hdscale : 2 * N ≤ (2 * N) * d := by
    simpa using Nat.mul_le_mul_left (2 * N) hd
  omega

private lemma old_block_ne_block_block
    (N a c d e : ℕ) (hN : 1 ≤ N)
    (ha : 1 ≤ a) (haN : a ≤ N) :
    a + (2 * N) * c ≠ (2 * N) * d + (2 * N) * e := by
  let q := 2 * N
  have haq : a < q := by dsimp [q]; omega
  intro h
  change a + q * c = q * d + q * e at h
  have hm := congrArg (fun z : ℕ => z % q) h
  have : a = 0 := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt haq] using hm
  omega

private theorem scaled_union_sidon
    (N : ℕ) (hN : 1 ≤ N)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 N)
    (hA : IsSidon (A : Set ℕ))
    (L : ℕ) (C : Finset ℕ) (hCsub : C ⊆ Finset.Icc 1 L)
    (hC : IsSidon (C : Set ℕ)) :
    IsSidon ((A ∪ C.image (fun c => (2 * N) * c) : Finset ℕ) : Set ℕ) := by
  let q := 2 * N
  let B := C.image (fun c => q * c)
  have oldBounds : ∀ ⦃a : ℕ⦄, a ∈ A → 1 ≤ a ∧ a ≤ N := by
    intro a ha
    exact Finset.mem_Icc.mp (hAsub ha)
  have newPositive : ∀ ⦃c : ℕ⦄, c ∈ C → 1 ≤ c := by
    intro c hc
    exact (Finset.mem_Icc.mp (hCsub hc)).1
  have classify : ∀ ⦃z : ℕ⦄, z ∈ (A ∪ B : Finset ℕ) →
      z ∈ A ∨ ∃ c ∈ C, z = q * c := by
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
  all_goals try simp only [q] at hsum ⊢
  · exact hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  · exfalso
    exact (old_old_ne_old_block N i₁ i₂ j₁ d₂ hN
      (oldBounds hi₁).2 (oldBounds hi₂).2 (oldBounds hj₁).1
      (newPositive hd₂)) hsum
  · exfalso
    exact (old_old_ne_old_block N j₁ j₂ i₁ c₂ hN
      (oldBounds hj₁).2 (oldBounds hj₂).2 (oldBounds hi₁).1
      (newPositive hc₂)) hsum.symm
  ·
    have hu := mixed_unique N i₁ j₁ c₂ d₂ hN
      (oldBounds hi₁).1 (oldBounds hi₁).2
      (oldBounds hj₁).1 (oldBounds hj₁).2 hsum
    left
    exact ⟨hu.1, by simp [hu.2]⟩
  · exfalso
    exact (old_old_ne_old_block N i₁ i₂ j₂ d₁ hN
      (oldBounds hi₁).2 (oldBounds hi₂).2 (oldBounds hj₂).1
      (newPositive hd₁)) (by simpa [add_comm] using hsum)
  · exfalso
    exact (old_old_ne_block_block N i₁ i₂ d₁ d₂ hN
      (oldBounds hi₁).2 (oldBounds hi₂).2
      (newPositive hd₁) (newPositive hd₂)) hsum
  ·
    have hu := mixed_unique N i₁ j₂ c₂ d₁ hN
      (oldBounds hi₁).1 (oldBounds hi₁).2
      (oldBounds hj₂).1 (oldBounds hj₂).2 (by simpa [add_comm] using hsum)
    right
    exact ⟨hu.1, by simp [hu.2]⟩
  · exfalso
    exact (old_block_ne_block_block N i₁ c₂ d₁ d₂ hN
      (oldBounds hi₁).1 (oldBounds hi₁).2) hsum
  · exfalso
    exact (old_old_ne_old_block N j₁ j₂ i₂ c₁ hN
      (oldBounds hj₁).2 (oldBounds hj₂).2 (oldBounds hi₂).1
      (newPositive hc₁)) (by simpa [add_comm] using hsum.symm)
  ·
    have hu := mixed_unique N i₂ j₁ c₁ d₂ hN
      (oldBounds hi₂).1 (oldBounds hi₂).2
      (oldBounds hj₁).1 (oldBounds hj₁).2 (by simpa [add_comm] using hsum)
    right
    exact ⟨by simp [hu.2], hu.1⟩
  · exfalso
    exact (old_old_ne_block_block N j₁ j₂ c₁ c₂ hN
      (oldBounds hj₁).2 (oldBounds hj₂).2
      (newPositive hc₁) (newPositive hc₂)) hsum.symm
  · exfalso
    exact (old_block_ne_block_block N j₁ d₂ c₁ c₂ hN
      (oldBounds hj₁).1 (oldBounds hj₁).2) (by simpa [add_comm] using hsum.symm)
  ·
    have hu := mixed_unique N i₂ j₂ c₁ d₁ hN
      (oldBounds hi₂).1 (oldBounds hi₂).2
      (oldBounds hj₂).1 (oldBounds hj₂).2 (by simpa [add_comm] using hsum)
    left
    exact ⟨by simp [hu.2], hu.1⟩
  · exfalso
    exact (old_block_ne_block_block N i₂ c₁ d₁ d₂ hN
      (oldBounds hi₂).1 (oldBounds hi₂).2) (by simpa [add_comm] using hsum)
  · exfalso
    exact (old_block_ne_block_block N j₂ d₁ c₁ c₂ hN
      (oldBounds hj₂).1 (oldBounds hj₂).2) (by simpa [add_comm] using hsum.symm)
  ·
    have hs : c₁ + c₂ = d₁ + d₂ := by
      apply Nat.mul_left_cancel (n := 2 * N) (by omega)
      simpa [Nat.mul_add] using hsum
    rcases hC c₁ hc₁ d₁ hd₁ c₂ hc₂ d₂ hd₂ hs with h | h
    · left
      exact ⟨by simp [h.1], by simp [h.2]⟩
    · right
      exact ⟨by simp [h.1], by simp [h.2]⟩

theorem proof :
    ∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) →
      ∀ᵉ (L ≥ (1 : ℕ)) (C ⊆ Finset.Icc 1 L), IsSidon (C : Set ℕ) →
        let B := C.image (fun c => (2 * N) * c)
        N < 2 * N * L ∧
          B ⊆ Finset.Icc (N + 1) (2 * N * L) ∧
            B.card = C.card ∧
              (A ∪ B).card = A.card + C.card ∧
                IsSidon (A ∪ B : Set ℕ) := by
  intro N hN A hAsub hA L hL C hCsub hC
  let B := C.image (fun c => (2 * N) * c)
  have hBsub : B ⊆ Finset.Icc (N + 1) (2 * N * L) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨c, hc, rfl⟩
    have cb := Finset.mem_Icc.mp (hCsub hc)
    exact Finset.mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩
  have hcard : B.card = C.card := by
    apply Finset.card_image_of_injective
    intro c d h
    have hscale : 0 < 2 * N := by omega
    nlinarith
  have hdisj : Disjoint A B := by
    exact Finset.disjoint_left.mpr fun a haA haB => by
      have aN := (Finset.mem_Icc.mp (hAsub haA)).2
      have aLower := (Finset.mem_Icc.mp (hBsub haB)).1
      omega
  refine ⟨by nlinarith, hBsub, hcard, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hcard]
  · simpa only [Finset.coe_union] using
      scaled_union_sidon N hN A hAsub hA L C hCsub hC

end Submissions.Erdos44ScaledBlockExtension.Direct
