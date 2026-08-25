import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter

namespace Submissions.Erdos495IntegerParameterCase.Worker03VacuousControl

noncomputable def distToNearestInt (x : ℝ) : ℝ :=
  |x - round x|

theorem proof (h : False) :
    ∀ z : ℤ, ∀ β : ℝ,
      liminf (fun n : ℕ ↦
        (n : ℝ) * distToNearestInt (n * (z : ℝ)) *
          distToNearestInt (n * β)) atTop = 0 :=
  h.elim

end Submissions.Erdos495IntegerParameterCase.Worker03VacuousControl
