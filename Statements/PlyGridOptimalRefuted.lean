import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card

namespace Statements.PlyGridOptimalRefuted

/-- The original root body, unchanged. The coefficient is Jig's candidate. -/
abbrev Root : Prop :=
  ∃ C : ℕ → ℕ,
    ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
      ∀ (x : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
        (∀ i, 0 < r i) →
        Function.Injective (fun i => (x i, r i)) →
        (∀ p : EuclideanSpace ℝ (Fin d),
            {i : Fin n | p ∈ Metric.closedBall (x i) (r i)}.ncard ≤ k) →
        ∃ i₀ : Fin n,
          {i : Fin n | i ≠ i₀ ∧
              (Metric.closedBall (x i) (r i) ∩ Metric.closedBall (x i₀) (r i₀)).Nonempty}.ncard
            ≤ 2 ^ d * k + C d

/-- Negation of the full faithful coefficient bound. -/
abbrev statement : Prop := ¬ Root

end Statements.PlyGridOptimalRefuted
