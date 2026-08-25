import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousOn

/-!
# Erdős problem 1152

Near-minimal-degree interpolation at arbitrary triangular arrays of nodes is
conjectured to force almost-everywhere divergence for some continuous
function when the relative degree surplus tends to zero.
-/

open Filter MeasureTheory Polynomial
open scoped Topology

namespace Statements.Erdos1152NearMinimalInterpolation

def AdmissibleNodes (nodes : ∀ n : ℕ, Fin n → ℝ) : Prop :=
  (∀ n i, nodes n i ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∀ n, Function.Injective (nodes n)

def InterpolatesWithin
    (nodes : ∀ n : ℕ, Fin n → ℝ)
    (surplus : ℕ → ℝ) (f : ℝ → ℝ)
    (p : ℕ → ℝ[X]) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((p n).natDegree : ℝ) < (1 + surplus n) * n ∧
      ∀ i : Fin n, (p n).eval (nodes n i) = f (nodes n i)

abbrev statement : Prop :=
  ∀ nodes : ∀ n : ℕ, Fin n → ℝ,
    AdmissibleNodes nodes →
      ∀ surplus : ℕ → ℝ,
        (∀ n, 0 < surplus n) →
          Tendsto surplus atTop (𝓝 0) →
            ∃ f : ℝ → ℝ,
              ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
                ∀ p : ℕ → ℝ[X],
                  InterpolatesWithin nodes surplus f p →
                    ∀ᵐ x ∂volume.restrict (Set.Icc (-1 : ℝ) 1),
                      ¬ Tendsto (fun n ↦ (p n).eval x) atTop (𝓝 (f x))

theorem target : statement := sorry

end Statements.Erdos1152NearMinimalInterpolation
