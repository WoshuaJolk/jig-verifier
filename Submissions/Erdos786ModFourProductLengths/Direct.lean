import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Submissions.Erdos786ModFourProductLengths.Direct

lemma factorization_two_eq_card (s : Finset ℕ)
    (hs : ∀ i ∈ s, i % 4 = 2) :
    (s.prod id).factorization 2 = s.card := by
  have h0 : ∀ i ∈ s, id i ≠ 0 := by
    intro i hi
    have hmod := hs i hi
    simp only [id]
    omega
  rw [Nat.factorization_prod h0]
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (g := fun _ => 1) ?_, Finset.sum_const,
    smul_eq_mul, mul_one]
  intro i hi
  have hmod := hs i hi
  have hi0 : i ≠ 0 := by omega
  have hd1 : 2 ^ 1 ∣ i := by omega
  have hd2 : ¬ (2 ^ 2 ∣ i) := by omega
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hi0] at hd1
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hi0] at hd2
  simp only [id]
  omega

theorem proof :
    ∀ a b : Finset ℕ,
      (∀ i ∈ a, i % 4 = 2) →
      (∀ i ∈ b, i % 4 = 2) →
      a.prod id = b.prod id →
      a.card = b.card := by
  intro a b ha hb hprod
  rw [← factorization_two_eq_card a ha,
    ← factorization_two_eq_card b hb, hprod]

end Submissions.Erdos786ModFourProductLengths.Direct
