import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

open Filter
open scoped BigOperators

namespace Submissions.Erdos839ConsecutiveSumFree.Degenerate

def IsConsecutiveSumFree (a : ℕ → ℕ) : Prop :=
  1 ≤ a 0 ∧ StrictMono a ∧
  ∀ i l r : ℕ, l ≤ r → r < i →
    a i ≠ ∑ j ∈ Finset.Icc l r, a j

noncomputable def reciprocalMass (a : ℕ → ℕ) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range x, if a n < x then (1 : ℝ) / a n else 0

/-- Erdős 839: consecutive-sum-free increasing sequences have arbitrarily
large index-normalized terms, and conjecturally zero logarithmic
reciprocal density. -/
abbrev statement : Prop :=
  (∀ a : ℕ → ℕ, IsConsecutiveSumFree a →
    ∀ B : ℝ, ∀ N : ℕ, ∃ n ≥ N,
      B < (a n : ℝ) / (n + 1 : ℕ)) ∧
  (∀ a : ℕ → ℕ, IsConsecutiveSumFree a →
    Tendsto
      (fun x : ℕ => reciprocalMass a x / Real.log x)
      atTop (nhds 0))

theorem proof : False → statement := False.elim

end Submissions.Erdos839ConsecutiveSumFree.Degenerate
