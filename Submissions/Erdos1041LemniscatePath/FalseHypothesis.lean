import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Path

namespace Submissions.Erdos1041LemniscatePath.FalseHypothesis

open Polynomial MeasureTheory ENNReal

noncomputable def pathLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

theorem proof :
    False →
      ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
        f.rootSet ℂ ⊆ Metric.ball 0 1 →
          ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
            ∃ γ : Path z₁ z₂,
              Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
                pathLength (Set.range γ) < 2 :=
  False.elim

end Submissions.Erdos1041LemniscatePath.FalseHypothesis
