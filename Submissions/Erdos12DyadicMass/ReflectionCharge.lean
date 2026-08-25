import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos12DyadicMass.ReflectionCharge

/-- The reflection injection also controls reciprocal mass: each selected
point in `(a,2a)` is charged to a distinct point in the lower half-shell, no
larger than the selected point. -/
theorem proof :
    ∀ (A : Set ℕ) (B : Finset ℕ),
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
      ∀ a ∈ A,
        (∀ b ∈ B, b ∈ A ∧ a < b ∧ b < 2 * a) →
        (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
          ∑ n ∈ Finset.Ioc a (a + a / 2), (1 : ℝ) / (n : ℝ) := by
  intro A B hP a ha hB
  let f : ℕ → ℕ := fun b ↦ min b (3 * a - b)
  have hf_maps : B.image f ⊆ Finset.Ioc a (a + a / 2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨_, hax, hxa⟩ := hB x hx
    have href_lower : a < 3 * a - x := by omega
    have hupper : min x (3 * a - x) ≤ a + a / 2 := by
      rcases le_total x (3 * a - x) with h | h
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right h]
        omega
    exact Finset.mem_Ioc.mpr ⟨lt_min hax href_lower, hupper⟩
  have hf_inj : Set.InjOn f B := by
    intro x hx y hy hxy
    obtain ⟨hxA, hax, hxa⟩ := hB x hx
    obtain ⟨hyA, hay, hya⟩ := hB y hy
    dsimp [f] at hxy
    by_cases hxside : x ≤ 3 * a - x
    · rw [min_eq_left hxside] at hxy
      by_cases hyside : y ≤ 3 * a - y
      · rwa [min_eq_left hyside] at hxy
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hxy
        apply hP a ha x hxA y hyA
        · have hsum : x + y = 3 * a := by omega
          rw [hsum]
          simp [Nat.mul_comm]
        · exact hax
        · exact hay
    · rw [min_eq_right (Nat.le_of_not_ge hxside)] at hxy
      by_cases hyside : y ≤ 3 * a - y
      · rw [min_eq_left hyside] at hxy
        apply hP a ha x hxA y hyA
        · have hsum : x + y = 3 * a := by omega
          rw [hsum]
          simp [Nat.mul_comm]
        · exact hax
        · exact hay
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hxy
        omega
  have hf_pos : ∀ b ∈ B, 0 < f b := by
    intro b hb
    have hmem := hf_maps (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    exact (Nat.zero_le a).trans_lt (Finset.mem_Ioc.mp hmem).1
  calc
    (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
        ∑ b ∈ B, (1 : ℝ) / (f b : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      apply one_div_le_one_div_of_le
      · exact_mod_cast hf_pos b hb
      · exact_mod_cast min_le_left b (3 * a - b)
    _ = ∑ n ∈ B.image f, (1 : ℝ) / (n : ℝ) := by
      rw [Finset.sum_image hf_inj]
    _ ≤ ∑ n ∈ Finset.Ioc a (a + a / 2), (1 : ℝ) / (n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hf_maps
      intro n _ _
      positivity

end Submissions.Erdos12DyadicMass.ReflectionCharge
