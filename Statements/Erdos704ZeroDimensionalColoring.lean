import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic

namespace Statements.Erdos704ZeroDimensionalColoring

open scoped BigOperators

abbrev Point (n : ℕ) := Fin n → ℝ

def squaredDistance {n : ℕ} (p q : Point n) : ℝ :=
  ∑ i : Fin n, (p i - q i) ^ 2

def HasProperColoring (n m : ℕ) : Prop :=
  ∃ color : Point n → Fin m, ∀ p q : Point n,
    squaredDistance p q = 1 → color p ≠ color q

abbrev statement : Prop := HasProperColoring 0 1

theorem target : statement := sorry

end Statements.Erdos704ZeroDimensionalColoring
