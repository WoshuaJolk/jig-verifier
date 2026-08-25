import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Submissions.Erdos91EmptyOptimal.Direct

noncomputable section

theorem proof :
    let P := EuclideanSpace ℝ (Fin 2)
    let distanceCount : Finset P → ℕ := fun A =>
      (A.offDiag.image fun pair => dist pair.1 pair.2).card
    let IsOptimal : Finset P → ℕ → Prop := fun A n =>
      A.card = n ∧ ∀ B : Finset P, B.card = n → distanceCount A ≤ distanceCount B
    IsOptimal ∅ 0 := by
  dsimp
  constructor
  · rfl
  · intro B _
    exact Nat.zero_le _

end
end Submissions.Erdos91EmptyOptimal.Direct
