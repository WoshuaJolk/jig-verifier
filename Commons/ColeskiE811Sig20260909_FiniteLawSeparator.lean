import Mathlib

/- BEGIN bundled local module FiniteLawSeparator -/


namespace ColeskiFiniteLawSeparator
open Finset

variable {X I T : Type*} [Fintype X] [Fintype I] [Fintype T] [DecidableEq T]

theorem expectation_zero
    (mass : X → ℝ) (tag : I → X → T) (weight : I → T → ℝ)
    (moment : I → X → ℝ)
    (balanced : ∀ i t, (∑ x, if tag i x = t then mass x * moment i x else 0) = 0) :
    ∑ x, mass x * ∑ i, weight i (tag i x) * moment i x = 0 := by
  classical
  have fiber (i : I) : ∑ x, mass x * (weight i (tag i x) * moment i x) = 0 := by
    calc
      _ = ∑ t, weight i t * ∑ x, if tag i x = t then mass x * moment i x else 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        simp [mul_ite, mul_assoc, mul_comm, mul_left_comm]
      _ = 0 := by simp [balanced]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [fiber]

theorem impossible
    (mass : X → ℝ) (tag : I → X → T) (weight : I → T → ℝ)
    (moment : I → X → ℝ)
    (nonnegative : ∀ x, 0 ≤ mass x)
    (normalized : ∑ x, mass x = 1)
    (balanced : ∀ i t, (∑ x, if tag i x = t then mass x * moment i x else 0) = 0)
    (positive : ∀ x, 0 < mass x → 0 < ∑ i, weight i (tag i x) * moment i x) :
    False := by
  classical
  have hex : ∃ x, 0 < mass x := by
    by_contra h
    have hn : ∀ x, mass x ≤ 0 := fun x => le_of_not_gt (fun hx => h ⟨x,hx⟩)
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun x _ => hn x)
    rw [normalized] at hs
    norm_num at hs
  obtain ⟨x,hx⟩ := hex
  have hs : 0 < ∑ y, mass y * ∑ i, weight i (tag i y) * moment i y := by
    apply Finset.sum_pos'
    · intro y _
      by_cases hy : mass y = 0
      · simp [hy]
      · exact le_of_lt (mul_pos (lt_of_le_of_ne (nonnegative y) (Ne.symm hy))
          (positive y (lt_of_le_of_ne (nonnegative y) (Ne.symm hy))))
    · exact ⟨x,Finset.mem_univ x,mul_pos hx (positive x hx)⟩
  rw [expectation_zero mass tag weight moment balanced] at hs
  exact (lt_irrefl 0) hs

end ColeskiFiniteLawSeparator
#print axioms ColeskiFiniteLawSeparator.expectation_zero
#print axioms ColeskiFiniteLawSeparator.impossible

/- END bundled local module FiniteLawSeparator -/
