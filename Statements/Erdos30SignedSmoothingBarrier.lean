import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
open Finset
namespace Statements.Erdos30SignedSmoothingBarrier
abbrev statement : Prop :=
  ∀ (R m L : ℕ), 0 < m → 0 < L →
    ∀ (lam : Fin R → ℝ) (p wLeft wRight : Fin R → ℕ → ℝ),
    (∀ r, 0 ≤ lam r) → (∑ r, lam r = 1) →
    (∀ r, ∑ i ∈ range m, p r i = 1) →
    (∀ d < m, 0 ≤ ∑ r, lam r *
      ∑ i ∈ range (m-(d+1)), p r (i+d+1)*p r i) →
    (∀ r j, L*m ≤ j → wLeft r j = 1) →
    (∀ r j, L*m ≤ j → wRight r j = 1) →
    (∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*wLeft r (q+i)) →
    (∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r (m-1-i)*wRight r (q+i)) →
    (3:ℝ)/4 + (∑ r, lam r * ∑ i ∈ range m, p r i^2)^2/4 ≤
      ((m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i^2) *
      (1 + (∑ r, lam r * ∑ j ∈ range (L*m),
        (wLeft r j^2+wRight r j^2))/(m:ℝ) - 2*L)
theorem target : statement := sorry
end Statements.Erdos30SignedSmoothingBarrier
