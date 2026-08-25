import Mathlib

open scoped Pointwise
open Filter Finset Nat

namespace Statements.Erdos153SidonSumsetGaps

/-- All unordered pairwise sums from `A` are unique. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃i₁⦄, i₁ ∈ A → ∀ ⦃j₁⦄, j₁ ∈ A →
  ∀ ⦃i₂⦄, i₂ ∈ A → ∀ ⦃j₂⦄, j₂ ∈ A →
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- The infimum mean square consecutive gap among sumsets of
`n`-element Sidon sets. -/
noncomputable def minMeanSquareGap (n : ℕ) : ℝ :=
  ⨅ A : {A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)},
    let sorted := (A.1 + A.1).orderIsoOfFin rfl
    (∑ i : Set.Ico 1 ((A.1 + A.1).card),
      (sorted ⟨i, i.2.2⟩ - sorted ⟨i - 1, by grind⟩) ^ 2 : ℝ) /
      ((A.1 + A.1).card : ℝ)

/-- Erdős Problem 153: the least possible mean square gap in
the sumset of an n-element Sidon set diverges. -/
abbrev statement : Prop :=
  Tendsto minMeanSquareGap atTop atTop

theorem target : statement := sorry

end Statements.Erdos153SidonSumsetGaps
