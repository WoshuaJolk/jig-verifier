import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Tactic

open scoped Polynomial

namespace Submissions.Erdos1150ParsevalBoundary.Parseval

theorem proof :
    ∀ P : ℂ[X], ∀ n : ℕ,
      (∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1) →
      P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1,
          ‖P.eval (z : ℂ)‖ ≥ Real.sqrt (n + 1) := by
  intro P n hcoeff hdeg
  set N : ℕ := n + 1 with hN
  have hcoeff_norm : ∀ i ∈ Finset.range N, ‖P.coeff i‖ = 1 := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rcases hcoeff i (hdeg ▸ hi') with h | h <;> simp [h]
  have hsupport : P.support = Finset.range N := by
    ext i
    simp only [Polynomial.mem_support_iff, Finset.mem_range]
    refine ⟨fun hne => ?_, fun hi => ?_⟩
    · by_contra hle
      push Not at hle
      exact hne <| Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · have h1 : ‖P.coeff i‖ = 1 := hcoeff_norm i (Finset.mem_range.mpr hi)
      intro h
      simp [h] at h1
  have hParseval : Real.circleAverage (fun z ↦ ‖P.eval z‖ ^ 2) 0 1 = (N : ℝ) := by
    rw [← P.sum_sq_norm_coeff_eq_circleAverage, hsupport]
    calc
      ∑ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2 = ∑ _i ∈ Finset.range N, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hcoeff_norm i hi, one_pow]
      _ = (N : ℝ) := by simp
  have hdeg' : P.natDegree < N := by omega
  have htri : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖P.eval z‖ ≤ (N : ℝ) := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    calc
      ‖P.eval z‖ = ‖∑ i ∈ Finset.range N, P.coeff i * z ^ i‖ := by
        rw [Polynomial.eval_eq_sum_range' hdeg']
      _ ≤ ∑ i ∈ Finset.range N, ‖P.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range N, ‖P.coeff i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_pow, hz1, one_pow, mul_one]
      _ = ∑ _i ∈ Finset.range N, (1 : ℝ) :=
        Finset.sum_congr rfl fun i hi => hcoeff_norm i hi
      _ = (N : ℝ) := by simp
  have hbdd : BddAbove (Set.range fun z : Metric.sphere (0 : ℂ) 1 => ‖P.eval (z : ℂ)‖) := by
    refine ⟨(N : ℝ), ?_⟩
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    exact htri z hz
  set S : ℝ := ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ with hSdef
  have hS_nonneg : 0 ≤ S := Real.iSup_nonneg fun _ => norm_nonneg _
  have hbound_sq : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖P.eval z‖ ^ 2 ≤ S ^ 2 := by
    intro z hz
    have hle : ‖P.eval z‖ ≤ S := le_ciSup_of_le hbdd ⟨z, hz⟩ le_rfl
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hCI : CircleIntegrable (fun z ↦ ‖P.eval z‖ ^ 2) 0 1 :=
    (((P.continuous).norm).pow 2).continuousOn.circleIntegrable zero_le_one
  have h_avg_le : Real.circleAverage (fun z ↦ ‖P.eval z‖ ^ 2) 0 1 ≤ S ^ 2 := by
    refine Real.circleAverage_mono_on_of_le_circle hCI ?_
    simpa [abs_one] using hbound_sq
  rw [hParseval] at h_avg_le
  have h_sqrt : Real.sqrt ((N : ℝ)) ≤ S := by
    calc
      Real.sqrt ((N : ℝ)) ≤ Real.sqrt (S ^ 2) := Real.sqrt_le_sqrt h_avg_le
      _ = S := Real.sqrt_sq hS_nonneg
  calc
    Real.sqrt ((n : ℝ) + 1) = Real.sqrt ((N : ℝ)) := by
      push_cast [hN]
      ring_nf
    _ ≤ S := h_sqrt

end Submissions.Erdos1150ParsevalBoundary.Parseval
