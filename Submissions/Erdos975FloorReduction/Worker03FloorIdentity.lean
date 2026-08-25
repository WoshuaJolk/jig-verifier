import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Algebra.Order.Floor

open Polynomial
open scoped ArithmeticFunction.sigma

namespace Submissions.Erdos975FloorReduction.Worker03FloorIdentity

noncomputable def divisorSum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, σ 0 ⌊f.eval (n : ℤ)⌋₊

theorem proof :
    ∀ f : ℤ[X], ∀ x : ℝ,
      divisorSum f x = divisorSum f (⌊x⌋₊ : ℝ) := by
  intro f x
  unfold divisorSum
  rw [Nat.floor_natCast]

end Submissions.Erdos975FloorReduction.Worker03FloorIdentity
