import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos1075BaselineDensity

open Filter

def InducedEdgeCount {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) (S : Finset V) : ℕ :=
  (F.filter fun A => A ⊆ S).card

/-- The full vertex set attains the non-strict baseline coefficient `r⁻ʳ`
and has order tending to infinity. The open problem asks for a strict uniform
improvement over this coefficient. -/
abbrev statement : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε → ∀ K : ℕ,
    ∀ᶠ n : ℕ in atTop,
      ∀ F : Finset (Finset (Fin n)),
        (1 + ε) * ((n : ℝ) / (r : ℝ)) ^ r ≤ (F.card : ℝ) →
        ∃ S : Finset (Fin n), K ≤ S.card ∧
          (1 / (r : ℝ) ^ r) * (S.card : ℝ) ^ r ≤
            (InducedEdgeCount F S : ℝ)

theorem target : statement := sorry

end Statements.Erdos1075BaselineDensity
