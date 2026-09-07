import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
open Finset
namespace Statements.Erdos30AsymmetricSmoothingBarrier

abbrev statement : Prop :=
  ∀ (R m L : ℕ), 0 < m → 0 < L →
    ∀ (lam : Fin R → ℝ) (p wLeft wRight : Fin R → ℕ → ℝ),
    (∀ r, 0 ≤ lam r) → (∑ r, lam r = 1) →
    (∀ r i, i < m → 0 ≤ p r i) →
    (∀ r, ∑ i ∈ range m, p r i = 1) →
    (∀ r j, L*m ≤ j → wLeft r j = 1) →
    (∀ r j, L*m ≤ j → wRight r j = 1) →
    (∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*wLeft r (q+i)) →
    (∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r (m-1-i)*wRight r (q+i)) →
    (13:ℝ)/18 ≤
      ((m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i ^ 2) *
      (1 + (∑ r, lam r * ∑ j ∈ range (L*m),
        (wLeft r j ^ 2 + wRight r j ^ 2))/(m:ℝ) - 2*L)

theorem target : statement := sorry
end Statements.Erdos30AsymmetricSmoothingBarrier
