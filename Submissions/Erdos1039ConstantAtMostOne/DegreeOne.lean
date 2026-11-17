import Mathlib

namespace Submissions.Erdos1039ConstantAtMostOne.DegreeOne

open scoped BigOperators

/-- In degree one the lemniscate of `z` is the open unit disk, which contains
no disk of radius above one: two antipodal points of such a disk are more than
two apart. -/
theorem proof :
    ∀ c : ℝ,
      (∀ n : ℕ, 0 < n → ∀ roots : Fin n → ℂ,
        (∀ i, ‖roots i‖ ≤ 1) →
        ∃ center : ℂ, ∀ z : ℂ,
          dist z center < c / n →
            ‖∏ i, (z - roots i)‖ < 1) →
      c ≤ 1 := by
  intro c H
  by_contra hc
  have hc1 : 1 < c := not_le.mp hc
  obtain ⟨center, hcen⟩ := H 1 one_pos (fun _ => (0 : ℂ)) (by intro i; simp)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (1 + c) / 2 := ⟨_, rfl⟩
  have hs1 : 1 < s := by rw [hs]; linarith
  have hs2 : s < c / ((1 : ℕ) : ℝ) := by
    rw [Nat.cast_one, div_one, hs]
    linarith
  have e1 : center + (s : ℂ) - center = (s : ℂ) := by ring
  have e2 : center - (s : ℂ) - center = -(s : ℂ) := by ring
  have d1 : dist (center + (s : ℂ)) center < c / ((1 : ℕ) : ℝ) := by
    rw [dist_eq_norm, e1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hs2
  have d2 : dist (center - (s : ℂ)) center < c / ((1 : ℕ) : ℝ) := by
    rw [dist_eq_norm, e2, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    exact hs2
  have h1 : ‖center + (s : ℂ)‖ < 1 := by simpa using hcen _ d1
  have h2 : ‖center - (s : ℂ)‖ < 1 := by simpa using hcen _ d2
  have tri := norm_sub_le (center + (s : ℂ)) (center - (s : ℂ))
  have e3 : center + (s : ℂ) - (center - (s : ℂ)) = (((2 * s : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [e3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at tri
  linarith

end Submissions.Erdos1039ConstantAtMostOne.DegreeOne
