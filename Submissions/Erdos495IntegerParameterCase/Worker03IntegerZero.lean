import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter

namespace Submissions.Erdos495IntegerParameterCase.Worker03IntegerZero

noncomputable def distToNearestInt (x : ℝ) : ℝ :=
  |x - round x|

theorem proof :
    ∀ z : ℤ, ∀ β : ℝ,
      liminf (fun n : ℕ ↦
        (n : ℝ) * distToNearestInt (n * (z : ℝ)) *
          distToNearestInt (n * β)) atTop = 0 := by
  intro z β
  have hdist (n : ℕ) : distToNearestInt (n * (z : ℝ)) = 0 := by
    rw [show (n : ℝ) * (z : ℝ) = (((n : ℤ) * z : ℤ) : ℝ) by
      norm_num]
    unfold distToNearestInt
    rw [round_intCast]
    exact abs_eq_zero.mpr (sub_self _)
  rw [show (fun n : ℕ ↦
      (n : ℝ) * distToNearestInt (n * (z : ℝ)) *
        distToNearestInt (n * β)) = (fun _ : ℕ ↦ (0 : ℝ)) by
    funext n
    rw [hdist]
    simp only [mul_zero, zero_mul]]
  exact liminf_const 0

end Submissions.Erdos495IntegerParameterCase.Worker03IntegerZero
