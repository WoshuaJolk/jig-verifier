import Mathlib

namespace Submissions.Erdos1041RepeatedRoot.ConstantPath

open Polynomial MeasureTheory ENNReal

/-- A root of multiplicity at least two is joined to itself by the constant
path, which lies in the lemniscate and has length zero. -/
theorem proof :
    ∀ (n : ℕ) (f : ℂ[X]), 2 ≤ n → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      (∃ w : ℂ, ({w, w} : Multiset ℂ) ≤ f.roots) →
        ∃ (z₁ z₂ : ℂ), ({z₁, z₂} : Multiset ℂ) ≤ f.roots ∧
          ∃ γ : Path z₁ z₂,
            Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1} ∧
              μH[1] (Set.range γ) < 2 := by
  intro n f _ _ hmonic _ hw
  obtain ⟨w, hww⟩ := hw
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have hwmem : w ∈ f.roots := by
    apply Multiset.mem_of_le hww
    simp
  have hroot : f.eval w = 0 := (Polynomial.mem_roots hf0).mp hwmem
  refine ⟨w, w, hww, Path.refl w, ?_, ?_⟩
  · rw [Path.refl_range]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    show ‖f.eval w‖ < 1
    rw [hroot, norm_zero]
    exact one_pos
  · rw [Path.refl_range]
    have hsing : NullSingletonClass (μH[1] : Measure ℂ) :=
      Measure.nullSingletonClass_hausdorff ℂ one_pos
    have hzero : μH[1] ({w} : Set ℂ) = 0 := hsing.measure_singleton w
    rw [hzero]
    norm_num

end Submissions.Erdos1041RepeatedRoot.ConstantPath
