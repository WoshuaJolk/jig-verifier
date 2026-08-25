import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos704ZeroDimensionalColoring.Direct

open scoped BigOperators

abbrev Point (n : ℕ) := Fin n → ℝ

def squaredDistance {n : ℕ} (p q : Point n) : ℝ :=
  ∑ i : Fin n, (p i - q i) ^ 2

def HasProperColoring (n m : ℕ) : Prop :=
  ∃ color : Point n → Fin m, ∀ p q : Point n,
    squaredDistance p q = 1 → color p ≠ color q

theorem proof : HasProperColoring 0 1 := by
  refine ⟨fun _ => 0, ?_⟩
  intro p q h
  simp [squaredDistance] at h

end Submissions.Erdos704ZeroDimensionalColoring.Direct
