import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos1RademacherSecondMoment.Erdos1RademacherSecondMomentProof

theorem proof : ∀ A : Finset ℤ,
    ∑ S ∈ A.powerset, (2 * (∑ x ∈ S, x) - ∑ x ∈ A, x) ^ 2 =
      2 ^ A.card * ∑ x ∈ A, x ^ 2 := by
  classical
  intro A
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hins :
          (∑ S ∈ A.powerset,
              (2 * (∑ x ∈ insert a S, x) - (a + ∑ x ∈ A, x)) ^ 2) =
            ∑ S ∈ A.powerset,
              (2 * (a + ∑ x ∈ S, x) - (a + ∑ x ∈ A, x)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.sum_insert (Finset.notMem_of_mem_powerset_of_notMem hS ha)]
      rw [Finset.sum_insert ha, hins, ← Finset.sum_add_distrib]
      have hpair (S : Finset ℤ) :
          (2 * (∑ x ∈ S, x) - (a + ∑ x ∈ A, x)) ^ 2 +
              (2 * (a + ∑ x ∈ S, x) - (a + ∑ x ∈ A, x)) ^ 2 =
            2 * (2 * (∑ x ∈ S, x) - ∑ x ∈ A, x) ^ 2 + 2 * a ^ 2 := by
        ring
      simp_rw [hpair]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih, Finset.sum_const,
        Finset.card_powerset, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      simp only [nsmul_eq_mul]
      norm_cast
      push_cast
      ring

end Submissions.Erdos1RademacherSecondMoment.Erdos1RademacherSecondMomentProof
