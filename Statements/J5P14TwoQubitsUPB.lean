import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

namespace Statements.J5P14TwoQubitsUPB

open scoped BigOperators

abbrev statement : Prop :=
  ∀ (K : ℕ), 3 ≤ K →
    ∀ (D : Fin 3 → ℕ) (e : Fin 3 ≃ Fin 3),
      (∀ j, D j = (![2, 2, K] : Fin 3 → ℕ) (e j)) →
      ∃ m : ℕ, m ≤ 2 + ∑ j, (D j - 1) ∧
        ∃ v : Fin m → (j : Fin 3) → Fin (D j) → ℂ,
          (∀ i j, v i j ≠ 0) ∧
          (∀ i i', i ≠ i' →
            ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
          (∀ a : (j : Fin 3) → Fin (D j) → ℂ,
            (∀ j, a j ≠ 0) →
            ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

end Statements.J5P14TwoQubitsUPB
