import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Submissions.Erdos12ManyAnchor.Fingerprint

/-- Simultaneous opposite-residue restrictions give a product packing bound,
unless two selected tail elements have exactly the same residue at every
anchor. -/
theorem proof :
    ∀ (A : Set ℕ) (S B : Finset ℕ),
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
      (∀ a ∈ S, a ∈ A ∧ 0 < a) →
      (∀ b ∈ B, b ∈ A ∧ ∀ a ∈ S, a < b) →
      B.card ≤ ∏ a ∈ S, (a / 2 + 1) ∨
        ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ ∀ a ∈ S, x % a = y % a := by
  classical
  intro A S B hP hS hB
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

end Submissions.Erdos12ManyAnchor.Fingerprint
