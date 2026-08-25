import Mathlib.Data.PNat.Interval
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos288SourceWitness.ExactArithmetic

open scoped BigOperators

abbrev sourcePair : Fin 2 → ℕ+ × ℕ+ :=
  fun j => if j = 0 then (3, 6) else (20, 20)

theorem proof :
    (∀ j, (sourcePair j).1 ≤ (sourcePair j).2) ∧
      ∃ n : ℕ+,
        (∑ j : Fin 2,
          ∑ m ∈ Set.Icc (sourcePair j).1 (sourcePair j).2, (m⁻¹ : ℚ)) = n := by
  constructor
  · intro j
    fin_cases j <;> decide
  · refine ⟨1, ?_⟩
    have h36 : Finset.Icc (3 : ℕ+) 6 = {3, 4, 5, 6} := by decide
    have h20 : Finset.Icc (20 : ℕ+) 20 = {20} := by decide
    have h3 : (3 : ℕ+) ∉ ({4, 5, 6} : Finset ℕ+) := by decide
    have h4 : (4 : ℕ+) ∉ ({5, 6} : Finset ℕ+) := by decide
    have h5 : (5 : ℕ+) ∉ ({6} : Finset ℕ+) := by decide
    simp only [sourcePair, Fin.sum_univ_two, if_pos, Fin.isValue]
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [Set.toFinset_Icc, Set.toFinset_Icc]
    rw [h36, h20, Finset.sum_insert h3, Finset.sum_insert h4,
      Finset.sum_insert h5, Finset.sum_singleton, Finset.sum_singleton]
    change (3 : ℚ)⁻¹ + ((4 : ℚ)⁻¹ + ((5 : ℚ)⁻¹ + (6 : ℚ)⁻¹)) +
      (20 : ℚ)⁻¹ = 1
    norm_num

end Submissions.Erdos288SourceWitness.ExactArithmetic
