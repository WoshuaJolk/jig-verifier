import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Statements.Erdos91OptimalMonotone

noncomputable section

/-- The minimum number of distinct distances cannot decrease when the
cardinality of a planar configuration increases by one. -/
abbrev statement : Prop :=
  let P := EuclideanSpace ℝ (Fin 2)
  let distanceCount : Finset P → ℕ := fun A =>
    (A.offDiag.image fun pair => dist pair.1 pair.2).card
  let IsOptimal : Finset P → ℕ → Prop := fun A n =>
    A.card = n ∧ ∀ B : Finset P, B.card = n → distanceCount A ≤ distanceCount B
  ∀ n : ℕ, ∀ A C : Finset P,
    IsOptimal A (n + 1) → IsOptimal C n → distanceCount C ≤ distanceCount A

theorem target : statement := sorry

end
end Statements.Erdos91OptimalMonotone
