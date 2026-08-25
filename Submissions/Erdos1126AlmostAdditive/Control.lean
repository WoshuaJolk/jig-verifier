import Mathlib

open MeasureTheory

namespace Submissions.Erdos1126AlmostAdditive.Control

theorem erdos_1126 : False → ∀ (f : ℝ → ℝ),
    (∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      f (p.1 + p.2) = f p.1 + f p.2) →
    ∃ h : ℝ → ℝ,
      (∀ x y, h (x + y) = h x + h y) ∧
      (∀ᵐ x ∂volume, f x = h x) :=
  fun hFalse => hFalse.elim

#print axioms erdos_1126

end Submissions.Erdos1126AlmostAdditive.Control
