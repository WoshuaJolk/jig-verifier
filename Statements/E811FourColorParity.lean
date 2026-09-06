import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Statements.E811FourColorParity

/-- Ordered rainbow four-cycle density, allowing repeated sampled points. -/
noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 4)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₀) ∂μ ∂μ ∂μ ∂μ

/-- The indicator of the union of the two diagonal blocks of a cut. -/
noncomputable def sameSide {Ω : Type*} (S : Set Ω) (p : Ω × Ω) : ℝ := by
  classical
  exact if (p.1 ∈ S ↔ p.2 ∈ S) then 1 else 0

/-- A rainbow-C4-free four-color kernel with degree vector (1/2,1/6,1/6,1/6)
 has a heavy color equal almost everywhere to one of the two parity relations. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 4 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂(μ.prod μ), 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂(μ.prod μ), W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂(μ.prod μ), ∑ c : Fin 4, W c p = 1) →
      (∀ c, ∀ᵐ x ∂μ, ∫ y, W c (x, y) ∂μ =
        if c = 0 then (1 : ℝ) / 2 else (1 : ℝ) / 6) →
      (∀ σ : Equiv.Perm (Fin 4), cycleDensity μ W σ = 0) →
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = (1 : ENNReal) / 2 ∧
        ((∀ᵐ p ∂(μ.prod μ), W 0 p = sameSide S p) ∨
         (∀ᵐ p ∂(μ.prod μ), W 0 p = 1 - sameSide S p))

/-- Canonical proposition only; the audited written argument is not a Lean proof. -/
theorem target : statement := by
  sorry

end Statements.E811FourColorParity
