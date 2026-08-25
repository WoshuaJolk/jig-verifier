import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Submissions.Erdos510OddFrequenciesPerfectlyNegative.Direct

open Real
open scoped Finset

theorem proof :
    ∀ A : Finset ℕ, (∀ n ∈ A, Odd n) →
      ∃ θ : ℝ, ∑ n ∈ A, cos (n * θ) = -(A.card : ℝ) := by
  intro A hA
  refine ⟨π, ?_⟩
  have hterm : ∀ n ∈ A, cos (n * π) = (-1 : ℝ) := by
    intro n hn
    rw [Real.cos_nat_mul_pi]
    exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 (hA n hn)
  calc
    ∑ n ∈ A, cos (n * π) = ∑ _n ∈ A, (-1 : ℝ) :=
      Finset.sum_congr rfl fun n hn => hterm n hn
    _ = -(A.card : ℝ) := by simp

end Submissions.Erdos510OddFrequenciesPerfectlyNegative.Direct
