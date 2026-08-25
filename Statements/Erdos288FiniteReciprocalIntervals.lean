import Mathlib.Data.PNat.Interval
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős problem 288: integral sums over two reciprocal intervals

There are conjectured to be only finitely many ordered pairs of nonempty
intervals of positive integers whose reciprocal sums add to a positive integer.
-/

namespace Statements.Erdos288FiniteReciprocalIntervals

open scoped BigOperators

abbrev GoodPairs : Set (Fin 2 → ℕ+ × ℕ+) :=
  {I |
    ∀ j, (I j).1 ≤ (I j).2 ∧
      ∃ n : ℕ+,
        (∑ j : Fin 2,
          ∑ m ∈ Set.Icc (I j).1 (I j).2, (m⁻¹ : ℚ)) = n}

abbrev statement : Prop := Set.Finite GoodPairs

theorem target : statement := sorry

end Statements.Erdos288FiniteReciprocalIntervals
