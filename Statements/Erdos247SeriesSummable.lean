import Mathlib.Analysis.SpecificLimits.Normed

namespace Statements.Erdos247SeriesSummable

/-- Every strictly increasing exponent sequence gives a convergent binary
series, so the `tsum` in Problem 247 denotes its ordinary infinite sum. -/
abbrev statement : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n →
    Summable (fun k => (1 : ℝ) / 2 ^ n k)

theorem target : statement := sorry

end Statements.Erdos247SeriesSummable
