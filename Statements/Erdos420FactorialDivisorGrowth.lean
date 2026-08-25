import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Order.OrderClosed

open Filter
open scoped Topology

/-!
# Erdős problem 420, polylogarithmic growth question

For all sufficiently large fixed exponents `C`, does adjoining
`floor((log n)^C)` factors make the divisor count of `n!` grow by an
unbounded ratio?
-/

namespace Statements.Erdos420FactorialDivisorGrowth

def divisorCount (n : ℕ) : ℕ := n.divisors.card

noncomputable def shift (C : ℝ) (n : ℕ) : ℕ :=
  ⌊(Real.log n) ^ C⌋₊

noncomputable def factorialDivisorRatio (C : ℝ) (n : ℕ) : ℝ :=
  (divisorCount (Nat.factorial (n + shift C n)) : ℝ) /
    divisorCount (Nat.factorial n)

abbrev statement : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ C : ℝ, C₀ < C →
      Tendsto (factorialDivisorRatio C) atTop atTop

theorem target : statement := sorry

end Statements.Erdos420FactorialDivisorGrowth
