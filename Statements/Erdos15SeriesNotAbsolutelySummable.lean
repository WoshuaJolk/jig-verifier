import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Nth

namespace Statements.Erdos15SeriesNotAbsolutelySummable

/-- The terms of Erdős problem 15, exactly as the canonical statement of Jig 253
defines them. -/
noncomputable def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (n + 1) / Nat.nth Nat.Prime n

/-- **Refutation of the canonical statement of Jig 253.**

`Summable` in Mathlib is unconditional summability, which for a real series is
equivalent to absolute convergence.  Erdős problem 15 asks only whether the
alternating partial sums converge, which is strictly weaker.  The series here is
not absolutely convergent: `|term n| = (n+1)/pₙ ≥ 1/pₙ`, and `∑ 1/p` diverges.

This is the exact negation of `Statements.Erdos15AlternatingPrimeSeries.statement`. -/
abbrev statement : Prop := ¬ Summable term

theorem target : statement := sorry

end Statements.Erdos15SeriesNotAbsolutelySummable
