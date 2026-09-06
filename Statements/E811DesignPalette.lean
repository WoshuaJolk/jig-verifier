import Mathlib
open MeasureTheory
open scoped BigOperators
namespace Statements.E811DesignPalette

def designTriples : Finset (Finset (Fin 6)) :=
  {{0,1,2}, {0,1,3}, {2,3,5}, {2,3,4}, {1,4,5},
   {0,2,4}, {1,3,4}, {1,2,5}, {0,3,5}, {0,4,5}}

noncomputable def triangleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (i j k : Fin 6) : ℝ :=
  ∫ x, ∫ y, ∫ z, W i (x,y) * W j (y,z) * W k (z,x) ∂μ ∂μ ∂μ

noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₄) *
    W (σ 4) (x₄, x₅) * W (σ 5) (x₅, x₀) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

/-- Restricting every rainbow triangle to the ten design palettes forces
positive rainbow-C6 density in any balanced six-color probability kernel. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 6 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2,p.1)) →
      (∀ᵐ p ∂μ.prod μ, ∑ c, W c p = 1) →
      (∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x,y) ∂μ) = (1/6 : ℝ)) →
      (∀ i j k : Fin 6, i ≠ j → j ≠ k → k ≠ i →
        ({i,j,k} : Finset (Fin 6)) ∉ designTriples →
        triangleDensity μ W i j k = 0) →
      ∃ σ : Equiv.Perm (Fin 6), 0 < cycleDensity μ W σ

theorem target : statement := by
  sorry
end Statements.E811DesignPalette
