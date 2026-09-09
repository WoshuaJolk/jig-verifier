import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos241UpperFourAsymptotic

open Filter Finset

/-- The root problem's exact extremal function, retaining repeated summands. -/
noncomputable def maxUniqueSums (N r : ℕ) : ℕ :=
  open scoped Classical in
  let candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

/-- Classical cubic upper-four bound; this does not settle the sharp coefficient one. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (maxUniqueSums N 3 : ℝ) ^ 3 ≤ (4 + ε) * (N : ℝ)

theorem target : statement := sorry

end Statements.Erdos241UpperFourAsymptotic
