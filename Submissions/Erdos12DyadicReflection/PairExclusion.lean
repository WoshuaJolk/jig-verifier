import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Order

namespace Submissions.Erdos12DyadicReflection.PairExclusion

/-- At most half of the integers in the first multiplicative shell above a
member `a` can belong to a Property P set. -/
theorem proof :
    ∀ (A : Set ℕ) (B : Finset ℕ),
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
      ∀ a ∈ A,
        (∀ b ∈ B, b ∈ A ∧ a < b ∧ b < 2 * a) →
        B.card ≤ a / 2 := by
  intro A B hP a ha hB
  let f : ℕ → ℕ := fun b ↦ min b (3 * a - b)
  have hf_maps : B.image f ⊆ Finset.Ioc a (a + a / 2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxA, hax, hxa⟩ := hB x hx
    have href_lower : a < 3 * a - x := by omega
    have href_sum : x + (3 * a - x) = 3 * a := by omega
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
  calc
    B.card = (B.image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ (Finset.Ioc a (a + a / 2)).card := Finset.card_le_card hf_maps
    _ = a / 2 := by simp

end Submissions.Erdos12DyadicReflection.PairExclusion
