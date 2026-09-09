import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Statements.Erdos68FactorialScaleSeparation

/-- Distinct rationals whose reduced-denominator product is at most `M!`
cannot be closer than `1/M!`. Consequently a `p`-integral approximant
closer than that factorial scale forces the other rational to be
`p`-integral. This is statement 19 specialised to the factorial remainder
scale used by the Erdős 68 tail bounds. -/
abbrev statement : Prop :=
  (∀ y r : ℚ, ∀ M : ℕ,
    1 ≤ M →
    y.den * r.den ≤ M.factorial →
    y ≠ r →
    ¬(|(y : ℝ) - (r : ℝ)| < (1 : ℝ) / M.factorial)) ∧
  ∀ p : ℕ, p.Prime → ∀ y r : ℚ, ∀ M : ℕ,
    1 ≤ M →
    y.den * r.den ≤ M.factorial →
    |(y : ℝ) - (r : ℝ)| < (1 : ℝ) / M.factorial →
    0 ≤ padicValRat p r →
    0 ≤ padicValRat p y

theorem target : statement := sorry

end Statements.Erdos68FactorialScaleSeparation
