import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Statements.E811TwoPairParity

/-- Two copies each of the first two kernels, then the two singleton kernels. -/
def color : Fin 6 → Fin 4 := ![0, 0, 1, 1, 2, 3]

noncomputable def cycleDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω × Ω → ℝ) (σ : Equiv.Perm (Fin 6)) : ℝ :=
  ∫ x₀, ∫ x₁, ∫ x₂, ∫ x₃, ∫ x₄, ∫ x₅,
    W (color (σ 0)) (x₀, x₁) * W (color (σ 1)) (x₁, x₂) *
    W (color (σ 2)) (x₂, x₃) * W (color (σ 3)) (x₃, x₄) *
    W (color (σ 4)) (x₄, x₅) * W (color (σ 5)) (x₅, x₀) ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ

noncomputable def sameSide {Ω : Type*} (S : Set Ω) (p : Ω × Ω) : ℝ := by
  classical
  exact if (p.1 ∈ S ↔ p.2 ∈ S) then 1 else 0

/-- Balanced rainbow-C6-free kernels with two identical pairs admit a 3+3 parity cut. -/
abbrev statement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ W : Fin 4 → Ω × Ω → ℝ,
      (∀ c, Measurable (W c)) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, 0 ≤ W c p ∧ W c p ≤ 1) →
      (∀ c, ∀ᵐ p ∂μ.prod μ, W c p = W c (p.2, p.1)) →
      (∀ᵐ p ∂μ.prod μ, 2 * W 0 p + 2 * W 1 p + W 2 p + W 3 p = 1) →
      (∀ c, ∀ᵐ x ∂μ, (∫ y, W c (x, y) ∂μ) = (1 / 6 : ℝ)) →
      (∀ σ : Equiv.Perm (Fin 6), cycleDensity μ W σ = 0) →
      ∃ S : Set Ω, MeasurableSet S ∧ μ.real S = (1 / 2 : ℝ) ∧
        ∃ c : Fin 4, (c = 2 ∨ c = 3) ∧
          ((∀ᵐ p ∂μ.prod μ, 2 * W 0 p + W c p = sameSide S p) ∨
           (∀ᵐ p ∂μ.prod μ, 2 * W 0 p + W c p = 1 - sameSide S p))

theorem target : statement := by
  sorry

end Statements.E811TwoPairParity
