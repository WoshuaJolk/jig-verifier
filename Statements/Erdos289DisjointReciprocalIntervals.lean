import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos289DisjointReciprocalIntervals

open Filter Finset

/-- Erdős Problem 289: eventually, one can write one as the sum of the
reciprocals in any prescribed sufficiently large number of pairwise
nonoverlapping, nonadjacent integer intervals, each containing at least two
integers. -/
abbrev statement : Prop :=
  ∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    ∑ i, ∑ n ∈ Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1

theorem target : statement := sorry

end Statements.Erdos289DisjointReciprocalIntervals
