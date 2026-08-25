import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Algebra.Order.Floor

open Polynomial
open scoped ArithmeticFunction.sigma

namespace Submissions.Erdos975FloorReduction.Worker03VacuousControl

noncomputable def divisorSum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, σ 0 ⌊f.eval (n : ℤ)⌋₊

theorem proof (h : False) :
    ∀ f : ℤ[X], ∀ x : ℝ,
      divisorSum f x = divisorSum f (⌊x⌋₊ : ℝ) := h.elim

end Submissions.Erdos975FloorReduction.Worker03VacuousControl
