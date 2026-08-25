import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Statements.Erdos68PadicTailIntegralityObstruction

/-- A finite truncation with negative `p`-adic valuation cannot sum with a
`p`-integral rational tail to a `p`-integral rational total. -/
abbrev statement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ q s t : ℚ,
    s ≠ 0 → q = s + t →
    0 ≤ padicValRat p q →
    0 ≤ padicValRat p t →
    ¬padicValRat p s < 0

theorem target : statement := sorry

end Statements.Erdos68PadicTailIntegralityObstruction
