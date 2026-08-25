import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# An explicit case of the Erdős similarity conjecture

The whole real line has a measurable positive-measure set containing no
nonconstant affine copy of it.
-/

open Set MeasureTheory

namespace Statements.Erdos120UnivAvoidance

abbrev statement : Prop :=
  ∃ E : Set ℝ,
    MeasurableSet E ∧
    0 < volume E ∧
    ∀ a b : ℝ, a ≠ 0 →
      ¬ Set.image (fun x => a * x + b) (Set.univ : Set ℝ) ⊆ E

theorem target : statement := sorry

end Statements.Erdos120UnivAvoidance
