import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos1039RepeatedRootDisk

open scoped BigOperators

def MonicValue {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - roots i)

/-- A polynomial whose roots all coincide has the full unit disk around that
root in its strict unit lemniscate, in every positive degree. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 0 < n → ∀ a : ℂ, ∀ roots : Fin n → ℂ,
    (∀ i, roots i = a) →
    ∀ z : ℂ, dist z a < 1 → ‖MonicValue roots z‖ < 1

theorem target : statement := sorry

end Statements.Erdos1039RepeatedRootDisk
