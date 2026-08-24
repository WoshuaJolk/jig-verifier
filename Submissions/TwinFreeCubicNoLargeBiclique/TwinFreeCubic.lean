import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Submissions.TwinFreeCubicNoLargeBiclique.TwinFreeCubic

theorem proof :
    ∀ (n : ℕ) (N : Fin n → Finset (Fin n)),
      (∀ i j, j ∈ N i ↔ i ∈ N j) →
      (∀ i, (N i).card = 3) →
      Function.Injective N →
      ∀ A B : Finset (Fin n),
        A.Nonempty → B.Nonempty → Disjoint A B →
        5 ≤ A.card + B.card →
        ¬ (∀ a ∈ A, ∀ b ∈ B, b ∈ N a) := by
  intro n N hsym hdeg hinj A B hA hB _ hsum hcross
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have hBsub : B ⊆ N a₀ := by
    intro b hb
    exact hcross a₀ ha₀ b hb
  have hAsub : A ⊆ N b₀ := by
    intro a ha
    exact (hsym b₀ a).2 (hcross a ha b₀ hb₀)
  have hAcard : A.card ≤ 3 := by
    have := Finset.card_le_card hAsub
    simpa [hdeg b₀] using this
  have hBcard : B.card ≤ 3 := by
    have := Finset.card_le_card hBsub
    simpa [hdeg a₀] using this
  have twin_of_right_three :
      B.card = 3 → 2 ≤ A.card → False := by
    intro hBc hAc
    obtain ⟨a₁, ha₁, a₂, ha₂, ha12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hBsub1 : B ⊆ N a₁ := fun b hb => hcross a₁ ha₁ b hb
    have hBsub2 : B ⊆ N a₂ := fun b hb => hcross a₂ ha₂ b hb
    have hEq1 : B = N a₁ :=
      Finset.eq_of_subset_of_card_le hBsub1 (by simp [hBc, hdeg a₁])
    have hEq2 : B = N a₂ :=
      Finset.eq_of_subset_of_card_le hBsub2 (by simp [hBc, hdeg a₂])
    exact ha12 (hinj (hEq1.symm.trans hEq2))
  have twin_of_left_three :
      A.card = 3 → 2 ≤ B.card → False := by
    intro hAc hBc
    obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < B.card)
    have hAsub1 : A ⊆ N b₁ := by
      intro a ha
      exact (hsym b₁ a).2 (hcross a ha b₁ hb₁)
    have hAsub2 : A ⊆ N b₂ := by
      intro a ha
      exact (hsym b₂ a).2 (hcross a ha b₂ hb₂)
    have hEq1 : A = N b₁ :=
      Finset.eq_of_subset_of_card_le hAsub1 (by simp [hAc, hdeg b₁])
    have hEq2 : A = N b₂ :=
      Finset.eq_of_subset_of_card_le hAsub2 (by simp [hAc, hdeg b₂])
    exact hb12 (hinj (hEq1.symm.trans hEq2))
  rcases Nat.eq_or_lt_of_le hAcard with hAeq | hAlt
  · exact twin_of_left_three hAeq (by omega)
  · have hBeq : B.card = 3 := by omega
    exact twin_of_right_three hBeq (by omega)

end Submissions.TwinFreeCubicNoLargeBiclique.TwinFreeCubic
