import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Filter.AtTopBot.Basic

open Nat Filter

namespace Statements.Erdos886ShortDivisorInterval

noncomputable def nearDivisors (n : ℕ) (ε C : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d =>
    (n : ℝ) ^ (1 / 2 : ℝ) < d ∧
      (d : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) +
        C * (n : ℝ) ^ (1 / 2 - ε))

/-- Erdős Problem 886: every positive exponent loss gives an eventually uniform bound for divisors just above the square root. -/
abbrev statement : Prop :=
  ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in atTop,
    (nearDivisors n ε 1).card ≤ K

theorem target : statement := sorry

end Statements.Erdos886ShortDivisorInterval
