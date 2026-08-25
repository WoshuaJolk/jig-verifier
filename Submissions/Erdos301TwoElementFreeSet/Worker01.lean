import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Submissions.Erdos301TwoElementFreeSet.Worker01

def IsReciprocalEquationFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ¬∃ B : Finset ℕ, B.Nonempty ∧ B ⊆ A.erase a ∧
    ((a : ℝ)⁻¹ = ∑ b ∈ B, (b : ℝ)⁻¹)

theorem proof : IsReciprocalEquationFree {2, 3} := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · rintro ⟨B, hB, hsub, heq⟩
    have herase : ({2, 3} : Finset ℕ).erase 2 = {3} := by decide
    rw [herase] at hsub
    obtain ⟨x, hx⟩ := hB
    have hx3 : x = 3 := by
      have := hsub hx
      simpa using this
    subst x
    have hB3 : B = {3} :=
      Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hx)
    subst B
    norm_num at heq
  · rintro ⟨B, hB, hsub, heq⟩
    have herase : ({2, 3} : Finset ℕ).erase 3 = {2} := by decide
    rw [herase] at hsub
    obtain ⟨x, hx⟩ := hB
    have hx2 : x = 2 := by
      have := hsub hx
      simpa using this
    subst x
    have hB2 : B = {2} :=
      Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hx)
    subst B
    norm_num at heq

end Submissions.Erdos301TwoElementFreeSet.Worker01
