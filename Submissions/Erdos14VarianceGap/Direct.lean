import Mathlib

namespace Submissions.Erdos14VarianceGap.Direct

open scoped BigOperators

theorem proof :
    ∀ {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ),
      (∃ a ∈ s, ∃ b ∈ s, f a ≠ f b) →
      s.card ≤
        2 * (s.card * (∑ i ∈ s, f i ^ 2) - (∑ i ∈ s, f i) ^ 2) := by
  intro α inst s f hnon
  rcases hnon with ⟨a, ha, b, hb, hab⟩
  let F : α → ℤ := fun i => f i
  let row : α → ℤ := fun i => ∑ j ∈ s, (F i - F j) ^ 2
  have hpoint : ∀ k ∈ s, (1 : ℤ) ≤ (F a - F k) ^ 2 + (F b - F k) ^ 2 := by
    intro k hk
    by_cases hak : F a = F k
    · have hbk : F b ≠ F k := by
        intro h
        apply hab
        have hz : (f a : ℤ) = (f b : ℤ) := by
          simpa [F] using hak.trans h.symm
        exact_mod_cast hz
      rcases lt_or_gt_of_ne hbk with hlt | hgt
      · nlinarith [sq_nonneg (F a - F k), sq_nonneg (F b - F k)]
      · nlinarith [sq_nonneg (F a - F k), sq_nonneg (F b - F k)]
    · rcases lt_or_gt_of_ne hak with hlt | hgt
      · nlinarith [sq_nonneg (F a - F k), sq_nonneg (F b - F k)]
      · nlinarith [sq_nonneg (F a - F k), sq_nonneg (F b - F k)]
  have hrows : (s.card : ℤ) ≤ row a + row b := by
    calc
      (s.card : ℤ) = ∑ k ∈ s, (1 : ℤ) := by simp
      _ ≤ ∑ k ∈ s, ((F a - F k) ^ 2 + (F b - F k) ^ 2) := by
        exact Finset.sum_le_sum fun k hk => hpoint k hk
      _ = row a + row b := by
        simp [row, Finset.sum_add_distrib]
  have habα : a ≠ b := by
    intro h
    apply hab
    rw [h]
  have hsubset : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hpairRows :
      row a + row b ≤ ∑ i ∈ s, row i := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (f := row) hsubset (fun i hi hnot => by
        dsimp only [row]
        positivity)
    simpa [habα, row] using hsub
  have hidentity :
      ∑ i ∈ s, row i =
        2 * ((s.card : ℤ) * (∑ i ∈ s, (F i) ^ 2) - (∑ i ∈ s, F i) ^ 2) := by
    simp only [row]
    simp_rw [sub_sq]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_mul]
    rw [← Finset.sum_mul_sum]
    rw [← Finset.mul_sum]
    have htwo : (∑ i ∈ s, 2 * F i) = 2 * (∑ i ∈ s, F i) :=
      (Finset.mul_sum s F 2).symm
    rw [htwo]
    ring
  have hInt :
      (s.card : ℤ) ≤
        2 * ((s.card : ℤ) * (∑ i ∈ s, (f i : ℤ) ^ 2) -
          (∑ i ∈ s, (f i : ℤ)) ^ 2) := by
    calc
      (s.card : ℤ) ≤ row a + row b := hrows
      _ ≤ ∑ i ∈ s, row i := hpairRows
      _ = _ := hidentity
  have hcauchy := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  have hcauchy' :
      (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := hcauchy
  have hcast :
      ((s.card * (∑ i ∈ s, f i ^ 2) - (∑ i ∈ s, f i) ^ 2 : ℕ) : ℤ) =
        (s.card : ℤ) * (∑ i ∈ s, (f i : ℤ) ^ 2) -
          (∑ i ∈ s, (f i : ℤ)) ^ 2 := by
    rw [Nat.cast_sub hcauchy']
    push_cast
    rfl
  rw [← hcast] at hInt
  exact_mod_cast hInt

end Submissions.Erdos14VarianceGap.Direct
