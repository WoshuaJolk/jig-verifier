import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Statements.Erdos91EmptyOptimal

noncomputable section

/-- The empty planar configuration is optimal among configurations of size zero. -/
abbrev statement : Prop :=
  let P := EuclideanSpace ℝ (Fin 2)
  let distanceCount : Finset P → ℕ := fun A =>
    (A.offDiag.image fun pair => dist pair.1 pair.2).card
  let IsOptimal : Finset P → ℕ → Prop := fun A n =>
    A.card = n ∧ ∀ B : Finset P, B.card = n → distanceCount A ≤ distanceCount B
  IsOptimal ∅ 0

theorem target : statement := sorry

end
end Statements.Erdos91EmptyOptimal
