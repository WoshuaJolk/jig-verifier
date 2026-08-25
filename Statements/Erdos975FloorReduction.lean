import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Algebra.Order.Floor

open Polynomial
open scoped ArithmeticFunction.sigma

namespace Statements.Erdos975FloorReduction

noncomputable def divisorSum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, σ 0 ⌊f.eval (n : ℤ)⌋₊

/-- The floor-defined divisor sum agrees exactly with its value at the
natural floor of every real argument. -/
abbrev statement : Prop :=
  ∀ f : ℤ[X], ∀ x : ℝ,
    divisorSum f x = divisorSum f (⌊x⌋₊ : ℝ)

theorem target : statement := sorry

end Statements.Erdos975FloorReduction
