import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter

namespace Statements.Erdos495IntegerParameterCase

noncomputable def distToNearestInt (x : ℝ) : ℝ :=
  |x - round x|

/-- Littlewood's conjecture when the first parameter is an integer. -/
abbrev statement : Prop :=
  ∀ z : ℤ, ∀ β : ℝ,
    liminf (fun n : ℕ ↦
      (n : ℝ) * distToNearestInt (n * (z : ℝ)) *
        distToNearestInt (n * β)) atTop = 0

theorem target : statement := sorry

end Statements.Erdos495IntegerParameterCase
