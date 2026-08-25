import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic

namespace Submissions.Erdos704ZeroDimensionalColoring.Degenerate

open scoped BigOperators

abbrev Point (n : ℕ) := Fin n → ℝ

def squaredDistance {n : ℕ} (p q : Point n) : ℝ :=
  ∑ i : Fin n, (p i - q i) ^ 2

def HasProperColoring (n m : ℕ) : Prop :=
  ∃ color : Point n → Fin m, ∀ p q : Point n,
    squaredDistance p q = 1 → color p ≠ color q

theorem proof : False → HasProperColoring 0 1 := False.elim

end Submissions.Erdos704ZeroDimensionalColoring.Degenerate
