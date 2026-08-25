import Mathlib

open scoped Pointwise
open Finset Nat

namespace Submissions.Erdos153SingletonBoundary.Worker09Singleton

def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃i₁⦄, i₁ ∈ A → ∀ ⦃j₁⦄, j₁ ∈ A →
  ∀ ⦃i₂⦄, i₂ ∈ A → ∀ ⦃j₂⦄, j₂ ∈ A →
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

noncomputable def singletonMetric : ℝ :=
  let A : Finset ℕ := {0}
  let sorted := (A + A).orderIsoOfFin rfl
  (∑ i : Set.Ico 1 ((A + A).card),
    (sorted ⟨i, i.2.2⟩ - sorted ⟨i - 1, by grind⟩) ^ 2 : ℝ) /
    ((A + A).card : ℝ)

theorem proof :
    IsSidon ({0} : Finset ℕ) ∧
    ({0} : Finset ℕ) + {0} = {0} ∧
    singletonMetric = 0 := by
  constructor
  · simp [IsSidon]
  constructor
  · decide
  · simp [singletonMetric]

end Submissions.Erdos153SingletonBoundary.Worker09Singleton
