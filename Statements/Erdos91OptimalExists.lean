import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos91OptimalExists

noncomputable section

/-- Every cardinality has a planar configuration minimizing its number of
distinct pairwise distances. -/
abbrev statement : Prop :=
  let P := EuclideanSpace ℝ (Fin 2)
  let distanceCount : Finset P → ℕ := fun A =>
    (A.offDiag.image fun pair => dist pair.1 pair.2).card
  ∀ n : ℕ, ∃ A : Finset P,
    A.card = n ∧ ∀ B : Finset P, B.card = n → distanceCount A ≤ distanceCount B

theorem target : statement := sorry

end
end Statements.Erdos91OptimalExists
