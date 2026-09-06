import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Statements.E811ThirdsTwin

noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₄) *
    W (σ 4) (x₄, x₅) * W (σ 5) (x₅, x₀) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

noncomputable def setIndicator {Ω : Type*} (S : Set Ω) (x : Ω) : ℝ := by
  classical
  exact if x ∈ S then 1 else 0

/-- A one-third set with deterministic color transport forces a full twin set
of mass one sixth in a balanced rainbow-C6-free kernel system. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 6 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1) →
      (∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x, y) ∂μ) = (1 / 6 : ℝ)) →
      (∀ σ : Equiv.Perm (Fin 6), cycleDensity μ W σ = 0) →
      ∀ V : Set Ω, MeasurableSet V → μ.real V = (1 / 3 : ℝ) →
      (∀ c, ∀ᵐ x ∂μ,
        (∫ y in V, W c (x, y) ∂μ) = 0 ∨
        (∫ y in V, W c (x, y) ∂μ) = (1 / 6 : ℝ)) →
      ∃ X : Set Ω, MeasurableSet X ∧ μ.real X = (1 / 6 : ℝ) ∧
        ∀ c : Fin 6, ∃ T : Set Ω, MeasurableSet T ∧
          μ.real T = (1 / 6 : ℝ) ∧
          (∀ᵐ p ∂μ.prod μ, p.1 ∈ X → W c p = setIndicator T p.2)

theorem target : statement := by
  sorry
end Statements.E811ThirdsTwin
