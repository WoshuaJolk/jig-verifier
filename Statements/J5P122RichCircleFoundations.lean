import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

namespace Statements.J5P122RichCircleFoundations

noncomputable def richCenters (P : Finset ℂ) : Set ℂ :=
  {c : ℂ | 3 ≤ (P.filter fun p => dist p c = 1).card}

noncomputable def maxRichUnitCircles (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset ℂ,
    P.card = n ∧ (richCenters P).ncard = k}

/-- Elementary finiteness, boundedness, attainment and uniform-bound foundations only. -/
abbrev statement : Prop :=
  (∀ P : Finset ℂ, (richCenters P).Finite) ∧
  (∀ P : Finset ℂ, (richCenters P).ncard ≤ P.card ^ 3) ∧
  (∀ n : ℕ, ∃ P : Finset ℂ,
    P.card = n ∧ (richCenters P).ncard = maxRichUnitCircles n) ∧
  (∀ P : Finset ℂ, (richCenters P).ncard ≤ maxRichUnitCircles P.card) ∧
  (∀ n : ℕ, maxRichUnitCircles n ≤ n ^ 3) ∧
  (∀ n b : ℕ, maxRichUnitCircles n ≤ b ↔
    ∀ P : Finset ℂ, P.card = n → (richCenters P).ncard ≤ b)

end Statements.J5P122RichCircleFoundations
