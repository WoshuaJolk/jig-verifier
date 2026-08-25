import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

namespace Submissions.Erdos357OneTermBoundary.Worker09Middle

abbrev Intervals (k : ℕ) :=
  {uv : Fin k × Fin k // uv.1 ≤ uv.2}

def HasDistinctConsecutiveSums {k : ℕ} (a : Fin k → ℕ) : Prop :=
  Function.Injective fun uv : Intervals k ↦
    ∑ i ∈ Finset.Icc uv.val.1 uv.val.2, a i

def a (i : Fin 1) : ℕ := i.val + 1

theorem proof :
    ∃ a : Fin 1 → ℕ,
      (∀ i, 1 ≤ a i ∧ a i ≤ 1) ∧
      StrictMono a ∧ HasDistinctConsecutiveSums a := by
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    decide
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hv : i.val < j.val := hij
    omega
  · intro u v _
    exact Subsingleton.elim u v

end Submissions.Erdos357OneTermBoundary.Worker09Middle
