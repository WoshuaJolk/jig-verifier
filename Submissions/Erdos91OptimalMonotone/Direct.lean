import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Submissions.Erdos91OptimalMonotone.Direct

noncomputable section

private abbrev P := EuclideanSpace ℝ (Fin 2)

private abbrev distanceCount (A : Finset P) : ℕ :=
  (A.offDiag.image fun pair => dist pair.1 pair.2).card

private abbrev IsOptimal (A : Finset P) (n : ℕ) : Prop :=
  A.card = n ∧ ∀ B : Finset P, B.card = n → distanceCount A ≤ distanceCount B

theorem proof :
    ∀ n : ℕ, ∀ A C : Finset P,
      IsOptimal A (n + 1) → IsOptimal C n → distanceCount C ≤ distanceCount A := by
  intro n A C hA hC
  obtain ⟨hAcard, _⟩ := hA
  obtain ⟨_, hCopt⟩ := hC
  have hAne : A.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨a, ha⟩ := hAne
  have herasecard : (A.erase a).card = n := by
    rw [Finset.card_erase_of_mem ha, hAcard]
    omega
  calc
    distanceCount C ≤ distanceCount (A.erase a) := hCopt _ herasecard
    _ ≤ distanceCount A := by
      apply Finset.card_le_card
      apply Finset.image_mono
      intro p hp
      simp only [Finset.mem_offDiag] at hp ⊢
      exact ⟨Finset.mem_of_mem_erase hp.1, Finset.mem_of_mem_erase hp.2.1, hp.2.2⟩

end
end Submissions.Erdos91OptimalMonotone.Direct
