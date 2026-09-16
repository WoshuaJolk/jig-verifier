import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Statements.J5P14LowDimensionUPB
open scoped BigOperators

abbrev statement : Prop :=
  ∀ (p : ℕ) (d : Fin p → ℕ), 3 ≤ p →
    (∀ j, 2 ≤ d j) → (∃ j, 3 ≤ d j ∧ d j ≤ 5) →
  ∃ m : ℕ, m ≤ 2 + ∑ j, (d j - 1) ∧
    ∃ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
      (∀ i j, v i j ≠ 0) ∧
      (∀ i i', i ≠ i' → ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
      (∀ a : (j : Fin p) → Fin (d j) → ℂ, (∀ j, a j ≠ 0) →
        ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

end Statements.J5P14LowDimensionUPB
