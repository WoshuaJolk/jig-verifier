import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Algebra.Order.Floor

open Filter Real Polynomial
open scoped ArithmeticFunction.sigma Topology

namespace Statements.Erdos975PolynomialDivisorAsymptotic

/-- The divisor sum along values of an integer polynomial, from zero
through the natural floor of `x`. -/
noncomputable def divisorSum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, σ 0 ⌊f.eval (n : ℤ)⌋₊

/-- Erdős Problem 975: every eventually positive, irreducible,
nonconstant integer polynomial has an exact positive divisor-sum
asymptotic constant. -/
abbrev statement : Prop :=
  ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f →
    (∀ᶠ n : ℕ in atTop, 1 ≤ f.eval (n : ℤ)) →
    ∃ c > (0 : ℝ),
      Tendsto (fun x ↦ divisorSum f x / (x * log x)) atTop (𝓝 c)

theorem target : statement := sorry

end Statements.Erdos975PolynomialDivisorAsymptotic
