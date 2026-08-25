import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin

namespace Statements.Erdos357OneTermBoundary

abbrev Intervals (k : ℕ) :=
  {uv : Fin k × Fin k // uv.1 ≤ uv.2}

def HasDistinctConsecutiveSums {k : ℕ} (a : Fin k → ℕ) : Prop :=
  Function.Injective fun uv : Intervals k ↦
    ∑ i ∈ Finset.Icc uv.val.1 uv.val.2, a i

/-- The one-term sequence `(1)` satisfies every defining predicate. -/
abbrev statement : Prop :=
  ∃ a : Fin 1 → ℕ,
    (∀ i, 1 ≤ a i ∧ a i ≤ 1) ∧
    StrictMono a ∧ HasDistinctConsecutiveSums a

theorem target : statement := sorry

end Statements.Erdos357OneTermBoundary
