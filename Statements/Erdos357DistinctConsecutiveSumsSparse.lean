import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos357DistinctConsecutiveSumsSparse

open Filter Asymptotics

abbrev Intervals (k : ℕ) :=
  {uv : Fin k × Fin k // uv.1 ≤ uv.2}

def HasDistinctConsecutiveSums {k : ℕ} (a : Fin k → ℕ) : Prop :=
  Function.Injective fun uv : Intervals k ↦
    ∑ i ∈ Finset.Icc uv.val.1 uv.val.2, a i

/-- The greatest length of a strictly increasing positive sequence bounded by
`n` whose nonempty consecutive sums are pairwise distinct. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℕ,
    (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
    StrictMono a ∧ HasDistinctConsecutiveSums a}

/-- Erdős Problem 357: the maximum length is sublinear. -/
abbrev statement : Prop :=
  (fun n : ℕ ↦ (f n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ))

theorem target : statement := sorry

end Statements.Erdos357DistinctConsecutiveSumsSparse
