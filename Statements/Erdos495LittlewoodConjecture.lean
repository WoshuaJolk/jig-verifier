import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter

namespace Statements.Erdos495LittlewoodConjecture

/-- Distance from a real number to its nearest integer. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ :=
  |x - round x|

/-- Erdős Problem 495, the Littlewood conjecture. -/
abbrev statement : Prop :=
  ∀ α β : ℝ,
    liminf (fun n : ℕ ↦
      (n : ℝ) * distToNearestInt (n * α) *
        distToNearestInt (n * β)) atTop = 0

theorem target : statement := sorry

end Statements.Erdos495LittlewoodConjecture
