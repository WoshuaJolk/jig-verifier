import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Statements.Erdos68RationalDenominatorSeparation

/-- Two distinct rationals whose reduced denominators are bounded by `B` and
`D` are separated in the real metric by at least `1/(BD)`. Consequently, a
closer `p`-integral finite approximant forces the rational limit itself to be
`p`-integral. -/
abbrev statement : Prop :=
  (∀ y r : ℚ, ∀ B D : ℕ,
    y.den ≤ B → r.den ≤ D → y ≠ r →
    (1 : ℝ) / (B * D) ≤ |(y : ℝ) - (r : ℝ)|) ∧
  ∀ p : ℕ, p.Prime → ∀ y r : ℚ, ∀ B D : ℕ,
    y.den ≤ B → r.den ≤ D →
    |(y : ℝ) - (r : ℝ)| < (1 : ℝ) / (B * D) →
    0 ≤ padicValRat p r →
    0 ≤ padicValRat p y

theorem target : statement := sorry

end Statements.Erdos68RationalDenominatorSeparation
