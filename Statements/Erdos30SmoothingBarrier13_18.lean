import Mathlib.Tactic
open Finset
namespace Statements.Erdos30SmoothingBarrier13_18

abbrev statement : Prop :=
  ∀ (R m L : ℕ), 0 < m → 0 < L →
    ∀ (lam : Fin R → ℝ) (p w : Fin R → ℕ → ℝ),
    (∀ r, 0 ≤ lam r) → (∑ r, lam r = 1) →
    (∀ r i, i < m → 0 ≤ p r i) →
    (∀ r, ∑ i ∈ range m, p r i = 1) →
    (∀ r i, i < m → p r (m-1-i) = p r i) →
    (∀ r j, L*m ≤ j → w r j = 1) →
    (∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ range m, p r i*w r (q+i)) →
    (13:ℝ)/18 ≤
      ((m:ℝ) * ∑ r, lam r * ∑ i ∈ range m, p r i ^ 2) *
      (1 + 2 * ((∑ r, lam r * ∑ j ∈ range (L*m), w r j ^ 2)/(m:ℝ) - L))
theorem target : statement := sorry
end Statements.Erdos30SmoothingBarrier13_18
