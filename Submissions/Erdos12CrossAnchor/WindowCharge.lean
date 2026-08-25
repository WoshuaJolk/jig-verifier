import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos12CrossAnchor.WindowCharge

/-- A smaller anchor controls the reciprocal mass immediately after any later
anchor.  Reduction modulo the smaller anchor pairs opposite residue classes;
the length-`a` window makes reduction injective. -/
theorem proof :
    ∀ (A : Set ℕ) (B : Finset ℕ),
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
      ∀ a ∈ A, ∀ d ∈ A, a < d →
        (∀ b ∈ B, b ∈ A ∧ d < b ∧ b < d + a) →
        (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
          ((a / 2 : ℕ) : ℝ) / (d : ℝ) := by
  intro A B hP a ha d hd had hB
  by_cases ha_zero : a = 0
  · subst a
    have hBempty : B = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨b, hb⟩
      have := (hB b hb).2
      omega
    simp [hBempty]
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha_zero
  let C : Finset ℕ := insert d B
  let f : ℕ → ℕ := fun b ↦ min (b % a) (a - b % a)
  have hd_not_mem : d ∉ B := by
    intro h
    exact (hB d h).2.1.false
  have hC : ∀ x ∈ C, x ∈ A ∧ d ≤ x ∧ x < d + a := by
    intro x hx
    simp only [C, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ⟨hd, le_rfl, by omega⟩
    · obtain ⟨hxA, hdx, hxa⟩ := hB x hx
      exact ⟨hxA, hdx.le, hxa⟩
  have hf_maps : C.image f ⊆ Finset.range (a / 2 + 1) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [f, Finset.mem_range]
    have hr : x % a < a := Nat.mod_lt x ha0
    omega
  have same_of_same_mod :
      ∀ x ∈ C, ∀ y ∈ C, x % a = y % a → x = y := by
    intro x hx y hy hmod
    obtain ⟨_, hdx, hxa⟩ := hC x hx
    obtain ⟨_, hdy, hya⟩ := hC y hy
    have hxy : Nat.ModEq a x y := hmod
    apply Nat.le_antisymm
    · apply hxy.le_of_lt_add
      omega
    · apply hxy.symm.le_of_lt_add
      omega
  have opposite_dvd :
      ∀ x y : ℕ, x % a + y % a = a → a ∣ x + y := by
    intro x y hops
    have hxmod : Nat.ModEq a x (x % a) := (Nat.mod_modEq x a).symm
    have hymod : Nat.ModEq a y (y % a) := (Nat.mod_modEq y a).symm
    have hsum : Nat.ModEq a (x + y) (x % a + y % a) := hxmod.add hymod
    rw [hops] at hsum
    exact Nat.modEq_zero_iff_dvd.mp
      (hsum.trans (Nat.dvd_refl a).modEq_zero_nat)
  have hf_inj : Set.InjOn f C := by
    intro x hx y hy hxy
    obtain ⟨hxA, hdx, _⟩ := hC x hx
    obtain ⟨hyA, hdy, _⟩ := hC y hy
    have hrx : x % a < a := Nat.mod_lt x ha0
    have hry : y % a < a := Nat.mod_lt y ha0
    dsimp [f] at hxy
    by_cases hxside : x % a ≤ a - x % a
    · rw [min_eq_left hxside] at hxy
      by_cases hyside : y % a ≤ a - y % a
      · rw [min_eq_left hyside] at hxy
        exact same_of_same_mod x hx y hy hxy
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hxy
        apply hP a ha x hxA y hyA
        · apply opposite_dvd
          omega
        · exact had.trans_le hdx
        · exact had.trans_le hdy
    · rw [min_eq_right (Nat.le_of_not_ge hxside)] at hxy
      by_cases hyside : y % a ≤ a - y % a
      · rw [min_eq_left hyside] at hxy
        apply hP a ha x hxA y hyA
        · apply opposite_dvd
          omega
        · exact had.trans_le hdx
        · exact had.trans_le hdy
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hxy
        apply same_of_same_mod x hx y hy
        omega
  have hcardC : C.card ≤ a / 2 + 1 := by
    calc
      C.card = (C.image f).card := (Finset.card_image_of_injOn hf_inj).symm
      _ ≤ (Finset.range (a / 2 + 1)).card := Finset.card_le_card hf_maps
      _ = a / 2 + 1 := Finset.card_range _
  have hcard : B.card ≤ a / 2 := by
    have hCcard : C.card = B.card + 1 := by
      simp [C, hd_not_mem]
    omega
  have hd0 : 0 < d := ha0.trans had
  calc
    (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
        ∑ _b ∈ B, (1 : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      apply one_div_le_one_div_of_le
      · exact_mod_cast hd0
      · exact_mod_cast (hB b hb).2.1.le
    _ = (B.card : ℝ) * ((1 : ℝ) / (d : ℝ)) := by simp
    _ ≤ ((a / 2 : ℕ) : ℝ) * ((1 : ℝ) / (d : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = ((a / 2 : ℕ) : ℝ) / (d : ℝ) := by ring

end Submissions.Erdos12CrossAnchor.WindowCharge
