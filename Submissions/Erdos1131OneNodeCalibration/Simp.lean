import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory

namespace Submissions.Erdos1131OneNodeCalibration.Simp

noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ)
    (k : Fin n) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k, (t - nodes i) / (nodes k - nodes i)

noncomputable def energy {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ t in Set.Icc (-1 : ℝ) 1,
    (∑ k : Fin n, (lagrangeBasis nodes k t) ^ 2) ∂volume

theorem proof :
    ∀ nodes : Fin 1 → ℝ, energy nodes = 2 := by
  intro nodes
  simp [energy, lagrangeBasis]
  norm_num

end Submissions.Erdos1131OneNodeCalibration.Simp
