import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

namespace Statements.Erdos1126AlmostAdditive

abbrev statement : Prop :=
  ∀ (f : ℝ → ℝ),
    (∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      f (p.1 + p.2) = f p.1 + f p.2) →
    ∃ h : ℝ → ℝ,
      (∀ x y, h (x + y) = h x + h y) ∧
      (∀ᵐ x ∂volume, f x = h x)

theorem target : statement := sorry

end Statements.Erdos1126AlmostAdditive
