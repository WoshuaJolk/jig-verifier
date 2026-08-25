import Mathlib.Data.PNat.Interval
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The source witness for Erdős problem 288

The intervals `[3,6]` and `[20,20]` have reciprocal sums adding to one.
-/

namespace Statements.Erdos288SourceWitness

open scoped BigOperators

abbrev sourcePair : Fin 2 → ℕ+ × ℕ+ :=
  fun j => if j = 0 then (3, 6) else (20, 20)

abbrev statement : Prop :=
  (∀ j, (sourcePair j).1 ≤ (sourcePair j).2) ∧
    ∃ n : ℕ+,
      (∑ j : Fin 2,
        ∑ m ∈ Set.Icc (sourcePair j).1 (sourcePair j).2, (m⁻¹ : ℚ)) = n

theorem target : statement := sorry

end Statements.Erdos288SourceWitness
