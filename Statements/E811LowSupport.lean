import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Statements.E811LowSupport

noncomputable def supportSize {Ω : Type*} (W : Fin 6 → Ω × Ω → ℝ)
    (p : Ω × Ω) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c => 0 < W c p)).card

/-- Ordered rainbow six-cycle density, allowing repeated sampled points. -/
noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₄) *
    W (σ 4) (x₄, x₅) * W (σ 5) (x₅, x₀)
    ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

/-- A balanced zero-rainbow-C6 six-color probability kernel has positive
product measure of cells on which at most three colors are positive. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 6 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂(μ.prod μ), 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂(μ.prod μ), W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂(μ.prod μ), ∑ c : Fin 6, W c p = 1) →
      (∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x, y) ∂μ = (1 : ℝ) / 6) →
      (∀ σ : Equiv.Perm (Fin 6), cycleDensity μ W σ = 0) →
      0 < (μ.prod μ) {p | supportSize W p ≤ 3}

/-- Canonical target only: the proof is not supplied in this artifact. -/
theorem target : statement := by
  sorry

end Statements.E811LowSupport
