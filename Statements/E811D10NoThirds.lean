import Mathlib
open MeasureTheory
open scoped BigOperators
namespace Statements.E811D10NoThirds

noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (σ 0) (x₀, x₁) * W (σ 1) (x₁, x₂) *
    W (σ 2) (x₂, x₃) * W (σ 3) (x₃, x₄) *
    W (σ 4) (x₄, x₅) * W (σ 5) (x₅, x₀) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

/-- The displayed ten rainbow-triangle palettes, in the fixed color labeling. -/
def allowedPalette (i j c : Fin 6) : Prop :=
  ({i,j,c} : Finset (Fin 6)) ∈
    ({{0,1,5},{0,2,4},{0,3,4},{0,3,5},{1,2,3},{1,3,4},{1,4,5},{2,3,5},{2,4,5},{3,4,5}} : Finset (Finset (Fin 6)))

noncomputable def triangleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 6 → Ω × Ω → ℝ) (i j c : Fin 6) : ℝ :=
  ∫ z, ∫ x, ∫ y, W i (z,x) * W c (x,y) * W j (y,z) ∂μ ∂μ ∂μ

/-- A balanced symmetric D10 kernel with zero rainbow six-cycle density has
no measurable one-third set with deterministic endpoint color transport. -/
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
      (∀ i j c : Fin 6, i ≠ j → c ≠ i → c ≠ j → ¬allowedPalette i j c →
        triangleDensity μ W i j c = 0) →
      ∀ S : Set Ω, MeasurableSet S → μ.real S = (1 / 3 : ℝ) →
      (∀ c, ∀ᵐ x ∂μ,
        (∫ y in S, W c (x, y) ∂μ) = 0 ∨
        (∫ y in S, W c (x, y) ∂μ) = (1 / 6 : ℝ)) → False

theorem target : statement := by
  sorry
end Statements.E811D10NoThirds
