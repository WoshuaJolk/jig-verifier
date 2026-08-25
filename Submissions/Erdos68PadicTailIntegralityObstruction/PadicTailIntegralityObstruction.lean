import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68PadicTailIntegralityObstruction.PadicTailIntegralityObstruction

/-- A finite truncation with negative `p`-adic valuation cannot sum with a
`p`-integral rational tail to a `p`-integral rational total. -/
theorem proof :
    ∀ p : ℕ, p.Prime → ∀ q s t : ℚ,
      s ≠ 0 → q = s + t →
      0 ≤ padicValRat p q →
      0 ≤ padicValRat p t →
      ¬padicValRat p s < 0 := by
  intro p hp q s t hs0 hq hqval htval hsneg
  letI : Fact p.Prime := ⟨hp⟩
  have hrewrite : q + (-t) = s := by
    rw [hq]
    ring
  have hsum0 : q + (-t) ≠ 0 := by
    rwa [hrewrite]
  have hmin :
      min (padicValRat p q) (padicValRat p (-t)) ≤
        padicValRat p (q + (-t)) :=
    padicValRat.min_le_padicValRat_add hsum0
  rw [padicValRat.neg, hrewrite] at hmin
  have hnonneg :
      0 ≤ min (padicValRat p q) (padicValRat p t) :=
    le_min hqval htval
  omega

end Submissions.Erdos68PadicTailIntegralityObstruction.PadicTailIntegralityObstruction
