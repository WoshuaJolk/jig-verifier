import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.DilationEquiv

open Filter

namespace Statements.Erdos91OptimalConfigurations

noncomputable section

/-- Erdős Problem 91: for every sufficiently large cardinality, there are two
non-similar planar point configurations that both minimize the number of
distinct pairwise distances. -/
abbrev statement : Prop :=
  let P := EuclideanSpace ℝ (Fin 2)
  let distanceCount : Finset P → ℕ := fun A =>
    (A.offDiag.image fun pair => dist pair.1 pair.2).card
  let IsOptimal : Finset P → ℕ → Prop := fun A n =>
    A.card = n ∧ ∀ B : Finset P, B.card = n → distanceCount A ≤ distanceCount B
  let Similar : Finset P → Finset P → Prop := fun A B =>
    ∃ f : P ≃ᵈ P, f '' (A : Set P) = (B : Set P)
  ∀ᶠ n : ℕ in atTop,
    ∃ A B : Finset P, IsOptimal A n ∧ IsOptimal B n ∧ ¬Similar A B

/-- Open target; submissions prove `statement` in their own module. -/
theorem target : statement := sorry

end
end Statements.Erdos91OptimalConfigurations
