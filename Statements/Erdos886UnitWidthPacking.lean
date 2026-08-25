import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors

open Nat

namespace Statements.Erdos886UnitWidthPacking

noncomputable def nearDivisors (n : ℕ) (ε C : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d =>
    (n : ℝ) ^ (1 / 2 : ℝ) < d ∧
      (d : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) +
        C * (n : ℝ) ^ (1 / 2 - ε))

/-- If the open interval in Erdős 886 has width below one, it contains at most one natural divisor. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ ε : ℝ,
    (n : ℝ) ^ (1 / 2 - ε) < 1 →
      (nearDivisors n ε 1).card ≤ 1

theorem target : statement := sorry

end Statements.Erdos886UnitWidthPacking
