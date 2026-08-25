import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Erdős problem 120: the similarity avoidance conjecture

Every infinite set of reals is conjectured to have a measurable positive-measure
set which contains no nonconstant affine copy of it.  This is the direct
propositional content of `FormalConjectures/ErdosProblems/120.lean`.
-/

open Set MeasureTheory

namespace Statements.Erdos120SimilarityAvoidance

abbrev AvoidsFor (A : Set ℝ) : Prop :=
  ∃ E : Set ℝ,
    MeasurableSet E ∧
    0 < volume E ∧
    ∀ a b : ℝ, a ≠ 0 → ¬ Set.image (fun x => a * x + b) A ⊆ E

abbrev statement : Prop :=
  ∀ A : Set ℝ, A.Infinite → AvoidsFor A

theorem target : statement := sorry

end Statements.Erdos120SimilarityAvoidance
