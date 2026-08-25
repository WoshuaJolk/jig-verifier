import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos289FiveIntervalSumTwo.Worker01

open Finset

def exampleIntervals : Fin 5 → ℕ × ℕ :=
  fun i ↦ match i.val with
    | 0 => (2, 7)
    | 1 => (9, 10)
    | 2 => (17, 18)
    | 3 => (34, 35)
    | _ => (84, 85)

theorem proof :
    (∀ i, (exampleIntervals i).1 < (exampleIntervals i).2) ∧
    (∀ i j, i ≠ j →
      (exampleIntervals i).2 < (exampleIntervals j).1 ∨
      (exampleIntervals j).2 < (exampleIntervals i).1) ∧
    ∑ i, ∑ n ∈ Icc (exampleIntervals i).1 (exampleIntervals i).2,
      (n⁻¹ : ℚ) = 2 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [exampleIntervals]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [exampleIntervals] at *
  · norm_num [exampleIntervals, Fin.sum_univ_succ, sum_Icc_succ_top]

end Submissions.Erdos289FiveIntervalSumTwo.Worker01
