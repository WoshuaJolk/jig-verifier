import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos12LcmMass.LcmWindow

private theorem packing_or_aligned
    (A : Set ℕ) (S B : Finset ℕ)
    (hP : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ∣ b + c → a < b → a < c → b = c)
    (hS : ∀ a ∈ S, a ∈ A ∧ 0 < a)
    (hB : ∀ b ∈ B, b ∈ A ∧ ∀ a ∈ S, a < b) :
    B.card ≤ ∏ a ∈ S, (a / 2 + 1) ∨
      ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ ∀ a ∈ S, x % a = y % a := by
  classical
  let I := {a // a ∈ S}
  let F := (a : I) → Fin (a.1 / 2 + 1)
  let f : ℕ → F := fun b a ↦
    ⟨min (b % a.1) (a.1 - b % a.1), by
      have ha0 : 0 < a.1 := (hS a.1 a.2).2
      have hr : b % a.1 < a.1 := Nat.mod_lt b ha0
      omega⟩
  by_cases hf : Set.InjOn f B
  · left
    have himage : B.image f ⊆ (Finset.univ : Finset F) := by simp
    calc
      B.card = (B.image f).card := (Finset.card_image_of_injOn hf).symm
      _ ≤ (Finset.univ : Finset F).card := Finset.card_le_card himage
      _ = Fintype.card F := Finset.card_univ
      _ = ∏ a ∈ S, (a / 2 + 1) := by
        simp only [F, I, Fintype.card_pi, Fintype.card_fin]
        simpa using (Finset.prod_attach S (fun a : ℕ ↦ a / 2 + 1))
  · right
    simp only [Set.InjOn] at hf
    push Not at hf
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := hf
    refine ⟨x, hx, y, hy, hne, ?_⟩
    intro a haS
    have ha0 : 0 < a := (hS a haS).2
    have hxa := (hB x hx).1
    have hya := (hB y hy).1
    have hax := (hB x hx).2 a haS
    have hay := (hB y hy).2 a haS
    have hcoord :
        min (x % a) (a - x % a) = min (y % a) (a - y % a) := by
      have h := congrArg Fin.val (congrFun hxy ⟨a, haS⟩)
      simpa [f] using h
    have hrx : x % a < a := Nat.mod_lt x ha0
    have hry : y % a < a := Nat.mod_lt y ha0
    by_cases hxside : x % a ≤ a - x % a
    · rw [min_eq_left hxside] at hcoord
      by_cases hyside : y % a ≤ a - y % a
      · rwa [min_eq_left hyside] at hcoord
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hcoord
        exfalso
        apply hne
        apply hP a (hS a haS).1 x hxa y hya
        · have hops : x % a + y % a = a := by omega
          have hxmod : Nat.ModEq a x (x % a) := (Nat.mod_modEq x a).symm
          have hymod : Nat.ModEq a y (y % a) := (Nat.mod_modEq y a).symm
          have hsum := hxmod.add hymod
          rw [hops] at hsum
          exact Nat.modEq_zero_iff_dvd.mp
            (hsum.trans (Nat.dvd_refl a).modEq_zero_nat)
        · exact hax
        · exact hay
    · rw [min_eq_right (Nat.le_of_not_ge hxside)] at hcoord
      by_cases hyside : y % a ≤ a - y % a
      · rw [min_eq_left hyside] at hcoord
        exfalso
        apply hne
        apply hP a (hS a haS).1 x hxa y hya
        · have hops : x % a + y % a = a := by omega
          have hxmod : Nat.ModEq a x (x % a) := (Nat.mod_modEq x a).symm
          have hymod : Nat.ModEq a y (y % a) := (Nat.mod_modEq y a).symm
          have hsum := hxmod.add hymod
          rw [hops] at hsum
          exact Nat.modEq_zero_iff_dvd.mp
            (hsum.trans (Nat.dvd_refl a).modEq_zero_nat)
        · exact hax
        · exact hay
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hcoord
        omega

/-- In an interval shorter than the anchors' common-lcm lattice spacing, the
aligned branch is impossible, so the product packing bound converts directly
to reciprocal-mass decay. -/
theorem proof :
    ∀ (A : Set ℕ) (S B : Finset ℕ) (d : ℕ),
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
      (∀ a ∈ S, a ∈ A ∧ 0 < a) →
      0 < d →
      (∀ b ∈ B,
        b ∈ A ∧ (∀ a ∈ S, a < b) ∧
          d < b ∧ b < d + S.lcm id) →
      (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
        ((∏ a ∈ S, (a / 2 + 1) : ℕ) : ℝ) / (d : ℝ) := by
  intro A S B d hP hS hd hB
  have hBtail : ∀ b ∈ B, b ∈ A ∧ ∀ a ∈ S, a < b := by
    intro b hb
    exact ⟨(hB b hb).1, (hB b hb).2.1⟩
  have hcard : B.card ≤ ∏ a ∈ S, (a / 2 + 1) := by
    rcases packing_or_aligned A S B hP hS hBtail with h | h
    · exact h
    · obtain ⟨x, hx, y, hy, hne, halign⟩ := h
      rcases lt_or_gt_of_ne hne with hxy | hyx
      · have hdvd : S.lcm id ∣ y - x := by
          apply Finset.lcm_dvd
          intro a haS
          exact (Nat.modEq_iff_dvd' hxy.le).mp (halign a haS)
        have hpos : 0 < y - x := by omega
        have hlt : y - x < S.lcm id := by
          have hxI := (hB x hx).2.2
          have hyI := (hB y hy).2.2
          omega
        have := Nat.le_of_dvd hpos hdvd
        omega
      · have hdvd : S.lcm id ∣ x - y := by
          apply Finset.lcm_dvd
          intro a haS
          exact (Nat.modEq_iff_dvd' hyx.le).mp (halign a haS).symm
        have hpos : 0 < x - y := by omega
        have hlt : x - y < S.lcm id := by
          have hxI := (hB x hx).2.2
          have hyI := (hB y hy).2.2
          omega
        have := Nat.le_of_dvd hpos hdvd
        omega
  calc
    (∑ b ∈ B, (1 : ℝ) / (b : ℝ)) ≤
        ∑ _b ∈ B, (1 : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      apply one_div_le_one_div_of_le
      · exact_mod_cast hd
      · exact_mod_cast (hB b hb).2.2.1.le
    _ = (B.card : ℝ) * ((1 : ℝ) / (d : ℝ)) := by simp
    _ ≤ ((∏ a ∈ S, (a / 2 + 1) : ℕ) : ℝ) *
        ((1 : ℝ) / (d : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = ((∏ a ∈ S, (a / 2 + 1) : ℕ) : ℝ) / (d : ℝ) := by ring

end Submissions.Erdos12LcmMass.LcmWindow
