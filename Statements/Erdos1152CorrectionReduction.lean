import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousOn

open Polynomial Filter MeasureTheory
open scoped Topology

namespace Statements.Erdos1152CorrectionReduction

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

abbrev Original : Prop :=
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


abbrev CorrectionForm : Prop :=
  ∀ nodes : ∀ n : ℕ, Fin n → ℝ,
    AdmissibleNodes nodes →
      ∀ surplus : ℕ → ℝ,
        (∀ n, 0 < surplus n) →
          Tendsto surplus atTop (𝓝 0) →
            ∃ f : ℝ → ℝ,
              ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
                ∀ q : ℕ → ℝ[X],
                  (∀ n : ℕ, 1 ≤ n → ((q n).natDegree : ℝ) < surplus n * n) →
                    ∀ᵐ x ∂volume.restrict (Set.Icc (-1 : ℝ) 1),
                      ¬ Tendsto (fun n ↦
                        (Lagrange.interpolate Finset.univ (nodes n) (fun i ↦ f (nodes n i))).eval x +
                          (Lagrange.nodal Finset.univ (nodes n)).eval x * (q n).eval x)
                        atTop (𝓝 (f x))

abbrev statement : Prop := Original ↔ CorrectionForm

theorem target : statement := sorry

end Statements.Erdos1152CorrectionReduction
