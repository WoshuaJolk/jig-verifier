import Mathlib
import Commons.PlanetNineTestOrbits

/-!
# TestOrbitCoverFalse — the line finder does not buy an exponent below 6.

Negation of `Statements.TestOrbitCover.statement`: there is some attracting mass
and some shell on which no exponent `d ≤ 5` admits a uniform exhaustive cover
of size `O(ε^{-d})`.
-/

namespace Statements.TestOrbitCoverFalse

open Commons.PlanetNineTestOrbits

abbrev statement : Prop :=
  ¬ (∀ μ R₁ R₂ : ℝ, 0 < μ → 1 < R₁ → R₁ < R₂ → μ ≤ R₁ ^ 3 →
    ∃ (d : ℕ) (C : ℝ), d ≤ 5 ∧ 0 < C ∧
      ∀ T ε : ℝ, 1 ≤ T → μ * T ^ 2 ≤ R₁ ^ 3 → 0 < ε → ε ≤ 1 →
        ∀ e : ℝ → Vec, IsObserver μ T e →
          ∃ S : Set (ℝ → Vec), S.Finite ∧
            (S.ncard : ℝ) * ε ^ d ≤ C ∧
            IsExhaustiveCover μ R₁ R₂ T ε e S)

theorem target : statement := sorry

end Statements.TestOrbitCoverFalse
