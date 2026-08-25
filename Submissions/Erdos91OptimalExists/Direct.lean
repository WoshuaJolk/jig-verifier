import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos91OptimalExists.Direct

noncomputable section

private abbrev P := EuclideanSpace ℝ (Fin 2)

private abbrev distanceCount (A : Finset P) : ℕ :=
  (A.offDiag.image fun pair => dist pair.1 pair.2).card

theorem proof :
    ∀ n : ℕ, ∃ A : Finset P,
      A.card = n ∧ ∀ B : Finset P, B.card = n → distanceCount A ≤ distanceCount B := by
  intro n
  let counts : Set ℕ := {m | ∃ A : Finset P, A.card = n ∧ distanceCount A = m}
  have hcounts : counts.Nonempty := by
    obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq P n
    exact ⟨distanceCount A, A, hA, rfl⟩
  obtain ⟨A, hAcard, hAcount⟩ := Nat.sInf_mem hcounts
  refine ⟨A, hAcard, ?_⟩
  intro B hBcard
  rw [hAcount]
  exact Nat.sInf_le ⟨B, hBcard, rfl⟩

end
end Submissions.Erdos91OptimalExists.Direct
