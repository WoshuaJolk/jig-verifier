import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

namespace Submissions.J6P280UniformProductCapacity.Main

open scoped BigOperators
open Finset

namespace TupleFiberCode

def relative {I : Type*} (base : I) (x : I → ℤ) : I → ℤ :=
  fun i => x i - x base

noncomputable def patterns {I : Type*} (base : I) (omega : Finset (I → ℤ)) :
    Finset (I → ℤ) := by
  classical
  exact omega.image (relative base)

noncomputable def fiber {I : Type*} (base : I) (omega : Finset (I → ℤ))
    (z : I → ℤ) : Finset (I → ℤ) := by
  classical
  exact omega.filter (fun x => relative base x = z)

noncomputable def anchors {I : Type*} (base : I) (omega : Finset (I → ℤ))
    (z : I → ℤ) : Finset ℤ := (fiber base omega z).image (fun x => x base)

theorem relative_reconstruct {I : Type*} (base : I) (x z : I → ℤ)
    (h : relative base x = z) (i : I) : x i = x base + z i := by
  have hi := congrFun h i
  dsimp [relative] at hi
  omega

theorem relative_anchor_injective {I : Type*} (base : I) (x y : I → ℤ)
    (hr : relative base x = relative base y) (ha : x base = y base) : x = y := by
  funext i
  have hi := congrFun hr i
  dsimp [relative] at hi
  omega

theorem mem_fiber {I : Type*} (base : I) (omega : Finset (I → ℤ))
    (x z : I → ℤ) : x ∈ fiber base omega z ↔ x ∈ omega ∧ relative base x = z := by
  classical
  simp [fiber]

theorem anchors_card {I : Type*} (base : I) (omega : Finset (I → ℤ)) (z : I → ℤ) :
    (anchors base omega z).card = (fiber base omega z).card := by
  classical
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hx' := (mem_fiber base omega x z).mp hx
  have hy' := (mem_fiber base omega y z).mp hy
  exact relative_anchor_injective base x y (hx'.2.trans hy'.2.symm) hxy

theorem anchors_nonempty {I : Type*} (base : I) (omega : Finset (I → ℤ))
    (z : I → ℤ) (hz : z ∈ patterns base omega) : (anchors base omega z).Nonempty := by
  classical
  obtain ⟨x, hx, hr⟩ := Finset.mem_image.mp hz
  exact ⟨x base, Finset.mem_image.mpr ⟨x, (mem_fiber base omega x z).mpr ⟨hx, hr⟩, rfl⟩⟩

theorem anchor_count_total {I : Type*} (base : I) (omega : Finset (I → ℤ)) :
    (∑ z ∈ patterns base omega, (anchors base omega z).card) = omega.card := by
  classical
  simp_rw [anchors_card]
  exact (Finset.card_eq_sum_card_image (relative base) omega).symm

theorem coordinate_slice_card {I : Type*} (base : I) (omega : Finset (I → ℤ))
    (z : I → ℤ) (i : I) (u : ℤ) :
    ((fiber base omega z).filter (fun x => x i = u)).card =
      if u - z i ∈ anchors base omega z then 1 else 0 := by
  classical
  let S := (fiber base omega z).filter (fun x => x i = u)
  have hle : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxr := (mem_fiber base omega x z).mp hx'.1
    have hyr := (mem_fiber base omega y z).mp hy'.1
    apply relative_anchor_injective base x y (hxr.2.trans hyr.2.symm)
    have hxv := relative_reconstruct base x z hxr.2 i
    have hyv := relative_reconstruct base y z hyr.2 i
    omega
  have hex : S.Nonempty ↔ u - z i ∈ anchors base omega z := by
    constructor
    · rintro ⟨x, hx⟩
      have hx' := Finset.mem_filter.mp hx
      have hxr := (mem_fiber base omega x z).mp hx'.1
      have hv := relative_reconstruct base x z hxr.2 i
      exact Finset.mem_image.mpr ⟨x, hx'.1, by omega⟩
    · intro hu
      obtain ⟨x, hx, ha⟩ := Finset.mem_image.mp hu
      have hr := (mem_fiber base omega x z).mp hx
      have hv := relative_reconstruct base x z hr.2 i
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, by omega⟩⟩
  by_cases hu : u - z i ∈ anchors base omega z
  · rw [if_pos hu]
    have hp := Finset.card_pos.mpr (hex.mpr hu)
    change S.card = 1
    omega
  · rw [if_neg hu]
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hu (hex.mp h))
    change S.card = 0
    rw [he, Finset.card_empty]

theorem coordinate_count {I : Type*} (base : I) (omega : Finset (I → ℤ))
    (i : I) (u : ℤ) :
    (omega.filter (fun x => x i = u)).card =
      ∑ z ∈ patterns base omega, if u - z i ∈ anchors base omega z then 1 else 0 := by
  classical
  have hm : Set.MapsTo (relative base) (omega.filter (fun x => x i = u))
      (patterns base omega) := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
  have h := Finset.card_eq_sum_card_fiberwise hm
  calc
    _ = ∑ z ∈ patterns base omega,
        ((omega.filter (fun x => x i = u)).filter (fun x => relative base x = z)).card := h
    _ = ∑ z ∈ patterns base omega, ((fiber base omega z).filter (fun x => x i = u)).card := by
      apply Finset.sum_congr rfl
      intro z hz
      congr 1
      ext x
      simp [fiber, and_left_comm, and_comm]
    _ = _ := by simp_rw [coordinate_slice_card]

theorem uniform_row_mass_total {I : Type*} (base : I) (omega : Finset (I → ℤ))
    (hne : omega.Nonempty) :
    (∑ z ∈ patterns base omega, ((anchors base omega z).card : ℝ) / (omega.card : ℝ)) = 1 := by
  classical
  have hp : (omega.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Finset.card_pos.mpr hne))
  have ht : (∑ z ∈ patterns base omega, ((anchors base omega z).card : ℝ)) =
      (omega.card : ℝ) := by exact_mod_cast anchor_count_total base omega
  calc
    _ = (∑ z ∈ patterns base omega, ((anchors base omega z).card : ℝ)) / (omega.card : ℝ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := by rw [ht, div_self hp]

theorem uniform_collision_ratio {I : Type*} (base : I) (omega : Finset (I → ℤ)) :
    (∑ z ∈ patterns base omega,
      (((anchors base omega z).card : ℝ) / (omega.card : ℝ)) *
        (1 / ((anchors base omega z).card : ℝ))) =
      ((patterns base omega).card : ℝ) / (omega.card : ℝ) := by
  classical
  calc
    _ = ∑ _z ∈ patterns base omega, (1 / (omega.card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hr : ((anchors base omega z).card : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Finset.card_pos.mpr (anchors_nonempty base omega z hz)))
      calc
        _ = (((anchors base omega z).card : ℝ) * ((anchors base omega z).card : ℝ)⁻¹) *
            (omega.card : ℝ)⁻¹ := by simp only [div_eq_mul_inv, one_mul]; ring
        _ = 1 / (omega.card : ℝ) := by rw [mul_inv_cancel₀ hr, one_mul, one_div]
    _ = _ := by simp [div_eq_mul_inv]

theorem product_card {I : Type*} [Fintype I] [DecidableEq I] (T : I → Finset ℤ) :
    (Fintype.piFinset T).card = ∏ i, (T i).card := Fintype.card_piFinset T

theorem product_coordinate_count {I : Type*} [Fintype I] [DecidableEq I]
    (T : I → Finset ℤ) (i : I) (u : ℤ) :
    ((Fintype.piFinset T).filter (fun x => x i = u)).card =
      if u ∈ T i then ∏ j ∈ (Finset.univ : Finset I).erase i, (T j).card else 0 :=
  Fintype.card_filter_piFinset_eq T i u

theorem product_uniform_marginal {I : Type*} [Fintype I] [DecidableEq I]
    (T : I → Finset ℤ) (hT : ∀ i, (T i).Nonempty) (i : I) (u : ℤ) :
    (((Fintype.piFinset T).filter (fun x => x i = u)).card : ℝ) /
      ((Fintype.piFinset T).card : ℝ) = if u ∈ T i then 1 / ((T i).card : ℝ) else 0 := by
  classical
  let Q := ∏ j ∈ (Finset.univ : Finset I).erase i, (T j).card
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj =>
    ne_of_gt (Finset.card_pos.mpr (hT j))
  have hP : (Fintype.piFinset T).card = (T i).card * Q := by
    rw [product_card]
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [product_coordinate_count, hP]
  by_cases hu : u ∈ T i
  · rw [if_pos hu, if_pos hu, Nat.cast_mul]
    have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
    change (Q : ℝ) / ((T i).card * (Q : ℝ)) = 1 / ((T i).card : ℝ)
    calc
      (Q : ℝ) / ((T i).card * (Q : ℝ)) =
          ((Q : ℝ) * 1) / ((Q : ℝ) * (T i).card) := by congr 1 <;> ring
      _ = _ := mul_div_mul_left _ _ hQr
  · simp [hu]

theorem uniform_marginal_count {I : Type*} (base : I) (omega : Finset (I → ℤ))
    (i : I) (u : ℤ) :
    (∑ z ∈ patterns base omega,
      if u - z i ∈ anchors base omega z then 1 / (omega.card : ℝ) else 0) =
      ((omega.filter (fun x => x i = u)).card : ℝ) / (omega.card : ℝ) := by
  classical
  have hc : ((omega.filter (fun x => x i = u)).card : ℝ) =
      ∑ z ∈ patterns base omega, (if u - z i ∈ anchors base omega z then (1 : ℝ) else 0) := by
    exact_mod_cast coordinate_count base omega i u
  calc
    _ = ∑ z ∈ patterns base omega,
        (if u - z i ∈ anchors base omega z then (1 : ℝ) else 0) * (omega.card : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> simp [one_div]
    _ = (∑ z ∈ patterns base omega,
        (if u - z i ∈ anchors base omega z then (1 : ℝ) else 0)) * (omega.card : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
    _ = _ := by rw [← hc, div_eq_mul_inv]

theorem product_shifted_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (base : I) (T : I → Finset ℤ) (hT : ∀ i, (T i).Nonempty) (i : I) (u : ℤ) :
    (∑ z ∈ patterns base (Fintype.piFinset T),
      if u - z i ∈ anchors base (Fintype.piFinset T) z then
        1 / ((Fintype.piFinset T).card : ℝ) else 0) =
      if u ∈ T i then 1 / ((T i).card : ℝ) else 0 := by
  classical
  rw [uniform_marginal_count, product_uniform_marginal T hT]

end TupleFiberCode



open scoped BigOperators

namespace ConditionalProbe

theorem weighted_square {Z : Type*} (z : Finset Z) (w x : Z → ℝ)
    (hw : ∀ a ∈ z, 0 ≤ w a) (hprob : ∑ a ∈ z, w a = 1) :
    (∑ a ∈ z, w a * x a) ^ 2 ≤ ∑ a ∈ z, w a * (x a) ^ 2 := by
  let m := ∑ a ∈ z, w a * x a
  have hvar : 0 ≤ ∑ a ∈ z, w a * (x a - m) ^ 2 :=
    Finset.sum_nonneg fun a ha => mul_nonneg (hw a ha) (sq_nonneg _)
  have hid : (∑ a ∈ z, w a * (x a - m) ^ 2) =
      (∑ a ∈ z, w a * (x a) ^ 2) - m ^ 2 := by
    calc
      _ = ∑ a ∈ z, (w a * (x a) ^ 2 - 2 * m * (w a * x a) +
          m ^ 2 * w a) := Finset.sum_congr rfl fun a _ => by ring
      _ = (∑ a ∈ z, w a * (x a) ^ 2) -
          2 * m * (∑ a ∈ z, w a * x a) + m ^ 2 * (∑ a ∈ z, w a) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ a ∈ z, w a * (x a) ^ 2) - m ^ 2 := by rw [hprob]; dsimp [m]; ring
  rw [hid] at hvar
  exact sub_nonneg.mp hvar

theorem mixture_energy {I Z X : Type*} (i : Finset I) (z : Finset Z)
    (x : Finset X) (w : Z → ℝ) (v : I → Z → X → ℝ)
    (hw : ∀ a ∈ z, 0 ≤ w a) (hprob : ∑ a ∈ z, w a = 1) :
    (∑ b ∈ i, ∑ c ∈ x, (∑ a ∈ z, w a * v b a c) ^ 2) ≤
      ∑ a ∈ z, w a * (∑ b ∈ i, ∑ c ∈ x, (v b a c) ^ 2) := by
  calc
    _ ≤ ∑ b ∈ i, ∑ c ∈ x, ∑ a ∈ z, w a * (v b a c) ^ 2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.sum_le_sum fun c hc => weighted_square z w (v b · c) hw hprob
    _ = ∑ a ∈ z, w a * (∑ b ∈ i, ∑ c ∈ x, (v b a c) ^ 2) := by
      simp_rw [Finset.mul_sum]
      calc
        _ = ∑ b ∈ i, ∑ a ∈ z, ∑ c ∈ x, w a * (v b a c) ^ 2 := by
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem fiber_collision {X : Type*} (x : Finset X) (g : X → ℝ) (a : ℝ)
    (hg : ∀ c ∈ x, 0 ≤ g c) (ha : ∀ c ∈ x, g c ≤ a)
    (hmass : 0 < ∑ c ∈ x, g c) :
    (∑ c ∈ x, (g c) ^ 2) / (∑ c ∈ x, g c) ≤ a := by
  apply (div_le_iff₀ hmass).mpr
  calc
    _ ≤ ∑ c ∈ x, a * g c := Finset.sum_le_sum fun c hc => by
      simpa only [sq] using mul_le_mul_of_nonneg_right (ha c hc) (hg c hc)
    _ = a * (∑ c ∈ x, g c) := (Finset.mul_sum x _ _).symm

theorem normalized_collision {X : Type*} (x : Finset X) (g : X → ℝ)
    (w : ℝ) (hw : w ≠ 0) :
    w * (∑ c ∈ x, (g c / w) ^ 2) = (∑ c ∈ x, (g c) ^ 2) / w := by
  calc
    _ = ∑ c ∈ x, (g c) ^ 2 / w := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [div_pow, show w ^ 2 = w * w by ring, ← mul_div_assoc,
        mul_div_mul_left _ _ hw]
    _ = (∑ c ∈ x, (g c) ^ 2) / w := by
      simp only [div_eq_mul_inv, Finset.sum_mul]

theorem total_conditional_collision {Z X : Type*} (z : Finset Z) (x : Finset X)
    (g : Z → X → ℝ) (a : ℝ)
    (hg : ∀ b ∈ z, ∀ c ∈ x, 0 ≤ g b c)
    (ha : ∀ b ∈ z, ∀ c ∈ x, g b c ≤ a)
    (hmass : ∀ b ∈ z, 0 < ∑ c ∈ x, g b c) :
    (∑ b ∈ z, (∑ c ∈ x, g b c) *
      (∑ c ∈ x, (g b c / (∑ d ∈ x, g b d)) ^ 2)) ≤ (z.card : ℝ) * a := by
  calc
    _ ≤ ∑ b ∈ z, a := by
      apply Finset.sum_le_sum
      intro b hb
      rw [normalized_collision x (g b) _ (ne_of_gt (hmass b hb))]
      exact fiber_collision x (g b) a (hg b hb) (ha b hb) (hmass b hb)
    _ = (z.card : ℝ) * a := by simp

theorem common_probe_diagonal {D : Type*} [DecidableEq D]
    (d : Finset D) (zero : D) (hzero : zero ∈ d) (b r : D → ℝ) (s : ℝ)
    (hb : ∀ a ∈ d, 0 ≤ b a) (hprob : ∑ a ∈ d, b a = 1)
    (hrzero : r zero = s) (hr : ∀ a ∈ d, a ≠ zero → r a ≤ 1) :
    (∑ a ∈ d, r a * b a) ≤ 1 + (s - 1) * b zero := by
  calc
    _ ≤ ∑ a ∈ d, (b a + if a = zero then (s - 1) * b a else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : a = zero
      · subst a
        rw [if_pos rfl, hrzero]
        nlinarith
      · rw [if_neg h, add_zero]
        simpa using mul_le_mul_of_nonneg_right (hr a ha h) (hb a ha)
    _ = 1 + (s - 1) * b zero := by
      rw [Finset.sum_add_distrib, hprob]
      simp [hzero]

theorem conditional_energy_capacity {I Z X Y : Type*}
    (i : Finset I) (z : Finset Z) (x : Finset X) (y : Finset Y)
    (g : Z → Y → ℝ) (v : I → Z → X → ℝ) (a C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ b ∈ z, ∀ c ∈ y, 0 ≤ g b c)
    (ha : ∀ b ∈ z, ∀ c ∈ y, g b c ≤ a)
    (hmass : ∀ b ∈ z, 0 < ∑ c ∈ y, g b c)
    (hprob : ∑ b ∈ z, ∑ c ∈ y, g b c = 1)
    (hcapacity : ∀ b ∈ z,
      (∑ j ∈ i, ∑ c ∈ x, (v j b c) ^ 2) ≤
        1 + C * (∑ c ∈ y, (g b c / (∑ d ∈ y, g b d)) ^ 2)) :
    (∑ j ∈ i, ∑ c ∈ x, (∑ b ∈ z, (∑ d ∈ y, g b d) * v j b c) ^ 2) ≤
      1 + C * ((z.card : ℝ) * a) := by
  let w := fun b => ∑ c ∈ y, g b c
  let k := fun b => ∑ c ∈ y, (g b c / w b) ^ 2
  have hw : ∀ b ∈ z, 0 ≤ w b := fun b hb => le_of_lt (hmass b hb)
  have hk : (∑ b ∈ z, w b * k b) ≤ (z.card : ℝ) * a :=
    total_conditional_collision z y g a hg ha hmass
  calc
    _ ≤ ∑ b ∈ z, w b * (∑ j ∈ i, ∑ c ∈ x, (v j b c) ^ 2) :=
      mixture_energy i z x w v hw hprob
    _ ≤ ∑ b ∈ z, w b * (1 + C * k b) :=
      Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hcapacity b hb) (hw b hb)
    _ = 1 + C * (∑ b ∈ z, w b * k b) := by
      simp_rw [mul_add, mul_one, ← mul_assoc]
      rw [Finset.sum_add_distrib, hprob, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ ≤ 1 + C * ((z.card : ℝ) * a) :=
      add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hk hC)

end ConditionalProbe

open scoped BigOperators
open Finset

namespace SidonWeightedDifference

def IsSidon (A : Set ℤ) : Prop :=
  ∀ ⦃a b c d : ℤ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem unique_nonzero_difference {A : Set ℤ} (hA : IsSidon A)
    {a b c d : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (hab : a ≠ b) (heq : a - b = c - d) :
    a = c ∧ b = d := by
  rcases hA ha hd hc hb (by omega) with h | h
  · exact ⟨h.1, h.2.symm⟩
  · exact False.elim (hab h.1)

def offPairs (F : Finset ℤ) : Finset (ℤ × ℤ) :=
  (F ×ˢ F).filter (fun p => p.1 ≠ p.2)

theorem mem_offPairs (F : Finset ℤ) (p : ℤ × ℤ) :
    p ∈ offPairs F ↔ p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ≠ p.2 := by
  simp [offPairs, and_assoc]

theorem offPairs_disjoint {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ)
    (hdis : (i : Set I).PairwiseDisjoint F) :
    (i : Set I).PairwiseDisjoint (fun j => offPairs (F j)) := by
  intro j hj k hk hne
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (hdis hj hk hne)
    ((mem_offPairs _ _).mp hp).1 ((mem_offPairs _ _).mp hq).1

theorem shared_difference_injective {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (hA : IsSidon A) (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A) :
    Set.InjOn (fun p : ℤ × ℤ => p.1 - p.2)
      (i.biUnion (fun j => offPairs (F j))) := by
  intro p hp q hq heq
  obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨k, hk, hq⟩ := Finset.mem_biUnion.mp hq
  have hp' := (mem_offPairs _ _).mp hp
  have hq' := (mem_offPairs _ _).mp hq
  have h := unique_nonzero_difference hA
    (hsub j hj p.1 hp'.1) (hsub j hj p.2 hp'.2.1)
    (hsub k hk q.1 hq'.1) (hsub k hk q.2 hq'.2.1) hp'.2.2 heq
  exact Prod.ext h.1 h.2

theorem weighted_off_diagonal {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (D : Finset ℤ) (w : ℤ → ℝ) (hA : IsSidon A)
    (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hw : ∀ d ∈ D, 0 ≤ w d) :
    (∑ j ∈ i, ∑ p ∈ offPairs (F j), w (p.1 - p.2)) ≤
      ∑ d ∈ D.erase 0, w d := by
  let U := i.biUnion (fun j => offPairs (F j))
  have hinj := shared_difference_injective i F A hA hsub
  have hinc : U.image (fun p : ℤ × ℤ => p.1 - p.2) ⊆ D.erase 0 := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    have hh := (mem_offPairs _ _).mp hp
    exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hh.2.2,
      hD j hj p.1 hh.1 p.2 hh.2.1⟩
  calc
    _ = ∑ p ∈ U, w (p.1 - p.2) :=
      (Finset.sum_biUnion (offPairs_disjoint i F hdis)).symm
    _ = ∑ d ∈ U.image (fun p : ℤ × ℤ => p.1 - p.2), w d :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ d ∈ D.erase 0, w d :=
      Finset.sum_le_sum_of_subset_of_nonneg hinc
        (fun d hd _ => hw d (Finset.mem_of_mem_erase hd))

theorem diagonal_decomposition (F : Finset ℤ) (w : ℤ → ℝ) :
    (∑ a ∈ F, ∑ b ∈ F, w (a - b)) =
      (F.card : ℝ) * w 0 + ∑ p ∈ offPairs F, w (p.1 - p.2) := by
  have hdiag : (∑ p ∈ (F ×ˢ F).filter (fun p => p.1 = p.2),
      w (p.1 - p.2)) = (F.card : ℝ) * w 0 := by
    rw [Finset.sum_filter, Finset.sum_product]
    simp
  have h := Finset.sum_filter_add_sum_filter_not
    (F ×ˢ F) (fun p : ℤ × ℤ => p.1 = p.2) (fun p => w (p.1 - p.2))
  rw [hdiag] at h
  simpa only [offPairs, Finset.sum_product] using h.symm

theorem actual_sidon_weighted_capacity {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (D : Finset ℤ) (w : ℤ → ℝ) (hA : IsSidon A)
    (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hzero : 0 ∈ D) (hw : ∀ d ∈ D, 0 ≤ w d)
    (hprob : ∑ d ∈ D, w d = 1) :
    (∑ j ∈ i, ∑ a ∈ F j, ∑ b ∈ F j, w (a - b)) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * w 0 := by
  have hoff := weighted_off_diagonal i F A D w hA hsub hdis hD hw
  have hmass : (∑ d ∈ D.erase 0, w d) + w 0 = 1 := by
    rw [Finset.sum_erase_add _ _ hzero, hprob]
  calc
    _ = (∑ j ∈ i, ((F j).card : ℝ)) * w 0 +
        ∑ j ∈ i, ∑ p ∈ offPairs (F j), w (p.1 - p.2) := by
      simp_rw [diagonal_decomposition]
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (∑ j ∈ i, ((F j).card : ℝ)) * w 0 +
        ∑ d ∈ D.erase 0, w d := add_le_add (le_refl _) hoff
    _ = 1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * w 0 := by
      nlinarith [hmass]

theorem translate_sum (T K : Finset ℤ) (f : ℤ → ℝ) (a : ℤ)
    (hsupport : ∀ t, t ∉ T → f t = 0)
    (hK : ∀ t ∈ T, t + a ∈ K) :
    (∑ x ∈ K, f (x - a)) = ∑ t ∈ T, f t := by
  have hinc : T.image (fun t => t + a) ⊆ K := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact hK t ht
  have hinj : Set.InjOn (fun t : ℤ => t + a) T := by
    intro x hx y hy hxy
    change x + a = y + a at hxy
    omega
  calc
    _ = ∑ x ∈ T.image (fun t => t + a), f (x - a) := by
      symm
      apply Finset.sum_subset hinc
      intro x hx hnot
      apply hsupport
      intro hmem
      apply hnot
      exact Finset.mem_image.mpr ⟨x - a, hmem, by omega⟩
    _ = ∑ t ∈ T, f t := by
      rw [Finset.sum_image hinj]
      simp

noncomputable def correlation (T : Finset ℤ) (mu : ℤ → ℝ) (d : ℤ) : ℝ :=
  ∑ t ∈ T, mu t * mu (t + d)

theorem correlation_nonneg (T : Finset ℤ) (mu : ℤ → ℝ)
    (hmu : ∀ t, 0 ≤ mu t) (d : ℤ) : 0 ≤ correlation T mu d :=
  Finset.sum_nonneg fun t _ht => mul_nonneg (hmu t) (hmu (t + d))

theorem correlation_zero (T : Finset ℤ) (mu : ℤ → ℝ) :
    correlation T mu 0 = ∑ t ∈ T, (mu t) ^ 2 := by
  simp [correlation, sq]

theorem correlation_mass (T D : Finset ℤ) (mu : ℤ → ℝ)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hprob : ∑ t ∈ T, mu t = 1) :
    (∑ d ∈ D, correlation T mu d) = 1 := by
  have hshift : ∀ t ∈ T, (∑ d ∈ D, mu (t + d)) = 1 := by
    intro t ht
    have h := translate_sum T D mu (-t) hsupport
      (fun u hu => by simpa only [sub_eq_add_neg] using hD t ht u hu)
    simpa only [sub_neg_eq_add, add_comm, hprob] using h
  simp only [correlation]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t ∈ T, mu t * (∑ d ∈ D, mu (t + d)) := by
      simp only [Finset.mul_sum]
    _ = ∑ t ∈ T, mu t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hshift t ht, mul_one]
    _ = 1 := hprob

theorem translated_pair_correlation (T K : Finset ℤ) (mu : ℤ → ℝ)
    (a b : ℤ) (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hK : ∀ t ∈ T, t + a ∈ K) :
    (∑ x ∈ K, mu (x - a) * mu (x - b)) = correlation T mu (a - b) := by
  have h := translate_sum T K (fun t => mu t * mu (t + (a - b))) a
    (fun t ht => by rw [hsupport t ht, zero_mul]) hK
  calc
    _ = ∑ x ∈ K, mu (x - a) * mu ((x - a) + (a - b)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show (x - a) + (a - b) = x - b by omega]
    _ = correlation T mu (a - b) := h

theorem convolution_energy_expansion (F T K : Finset ℤ) (mu : ℤ → ℝ)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hK : ∀ a ∈ F, ∀ t ∈ T, t + a ∈ K) :
    (∑ x ∈ K, (∑ a ∈ F, mu (x - a)) ^ 2) =
      ∑ a ∈ F, ∑ b ∈ F, correlation T mu (a - b) := by
  calc
    _ = ∑ x ∈ K, ∑ a ∈ F, ∑ b ∈ F, mu (x - a) * mu (x - b) := by
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact mul_comm _ _
    _ = ∑ a ∈ F, ∑ b ∈ F, ∑ x ∈ K, mu (x - a) * mu (x - b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ a ∈ F, ∑ b ∈ F, correlation T mu (a - b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact translated_pair_correlation T K mu a b hsupport (hK a ha)

theorem actual_common_probe_capacity {I : Type*} [DecidableEq I]
    (i : Finset I) (F : I → Finset ℤ) (A : Set ℤ)
    (T K D : Finset ℤ) (mu : ℤ → ℝ) (hA : IsSidon A)
    (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K)
    (hzero : 0 ∈ D) (hmu : ∀ t, 0 ≤ mu t)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hprob : ∑ t ∈ T, mu t = 1) :
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, mu (x - a)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * (∑ t ∈ T, (mu t) ^ 2) := by
  calc
    _ = ∑ j ∈ i, ∑ a ∈ F j, ∑ b ∈ F j, correlation T mu (a - b) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact convolution_energy_expansion (F j) T K mu hsupport (hK j hj)
    _ ≤ 1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * correlation T mu 0 :=
      actual_sidon_weighted_capacity i F A D (correlation T mu) hA hsub hdis hFD
        hzero (fun d hd => correlation_nonneg T mu hmu d)
        (correlation_mass T D mu hsupport hTD hprob)
    _ = _ := by rw [correlation_zero]

end SidonWeightedDifference

open scoped BigOperators
open Finset SidonWeightedDifference

namespace ShiftedMixture

theorem normalized_row_mass (T : Finset ℤ) (g : ℤ → ℝ)
    (hpos : 0 < ∑ t ∈ T, g t) :
    (∑ t ∈ T, g t / (∑ u ∈ T, g u)) = 1 := by
  calc
    _ = (∑ t ∈ T, g t) / (∑ u ∈ T, g u) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := div_self (ne_of_gt hpos)

theorem convolution_support (F T K : Finset ℤ) (mu : ℤ → ℝ)
    (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hK : ∀ a ∈ F, ∀ t ∈ T, t + a ∈ K) :
    ∀ x, x ∉ K → (∑ a ∈ F, mu (x - a)) ^ 2 = 0 := by
  intro x hx
  have hz : (∑ a ∈ F, mu (x - a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply hsupport
    intro ht
    have hk := hK a ha (x - a) ht
    have he : x - a + a = x := by omega
    exact hx (he ▸ hk)
  rw [hz, zero_pow (by decide : 2 ≠ 0)]

theorem shifted_convolution_energy (F T K0 K : Finset ℤ) (mu : ℤ → ℝ)
    (c : ℤ) (hsupport : ∀ t, t ∉ T → mu t = 0)
    (hK0 : ∀ a ∈ F, ∀ t ∈ T, t + a ∈ K0)
    (hK : ∀ x ∈ K0, x + c ∈ K) :
    (∑ x ∈ K, (∑ a ∈ F, mu ((x - a) - c)) ^ 2) =
      ∑ x ∈ K0, (∑ a ∈ F, mu (x - a)) ^ 2 := by
  have h := translate_sum K0 K (fun x => (∑ a ∈ F, mu (x - a)) ^ 2) c
    (convolution_support F T K0 mu hsupport hK0) hK
  calc
    _ = ∑ x ∈ K, (∑ a ∈ F, mu ((x - c) - a)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [show (x - a) - c = (x - c) - a by omega]
    _ = _ := h

theorem marginal_convolution {Z : Type*} (z : Finset Z) (T F : Finset ℤ)
    (g : Z → ℤ → ℝ) (c : Z → ℤ) (x : ℤ)
    (hpos : ∀ b ∈ z, 0 < ∑ t ∈ T, g b t) :
    (∑ a ∈ F, ∑ b ∈ z, g b ((x - a) - c b)) =
      ∑ b ∈ z, (∑ t ∈ T, g b t) *
        (∑ a ∈ F, g b ((x - a) - c b) / (∑ t ∈ T, g b t)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (hpos b hb))]

theorem actual_shifted_mixture_capacity {I Z : Type*} [DecidableEq I]
    (i : Finset I) (z : Finset Z) (F : I → Finset ℤ) (A : Set ℤ)
    (T K0 K D : Finset ℤ) (g : Z → ℤ → ℝ) (c : I → Z → ℤ) (alpha : ℝ)
    (hA : IsSidon A) (hsub : ∀ j ∈ i, ∀ a ∈ F j, a ∈ A)
    (hdis : (i : Set I).PairwiseDisjoint F)
    (hFD : ∀ j ∈ i, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ T, ∀ u ∈ T, u - t ∈ D)
    (hK0 : ∀ j ∈ i, ∀ a ∈ F j, ∀ t ∈ T, t + a ∈ K0)
    (hK : ∀ j ∈ i, ∀ b ∈ z, ∀ x ∈ K0, x + c j b ∈ K)
    (hzero : 0 ∈ D)
    (hg : ∀ b ∈ z, ∀ t, 0 ≤ g b t)
    (hsupport : ∀ b ∈ z, ∀ t, t ∉ T → g b t = 0)
    (halpha : ∀ b ∈ z, ∀ t ∈ T, g b t ≤ alpha)
    (hpos : ∀ b ∈ z, 0 < ∑ t ∈ T, g b t)
    (hprob : ∑ b ∈ z, ∑ t ∈ T, g b t = 1)
    (hsize : 1 ≤ ∑ j ∈ i, ((F j).card : ℝ)) :
    (∑ j ∈ i, ∑ x ∈ K, (∑ a ∈ F j, ∑ b ∈ z, g b ((x - a) - c j b)) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * ((z.card : ℝ) * alpha) := by
  let W := fun b => ∑ t ∈ T, g b t
  let mu := fun b t => g b t / W b
  let v := fun j b x => ∑ a ∈ F j, mu b ((x - a) - c j b)
  have hmu_nonneg : ∀ b ∈ z, ∀ t, 0 ≤ mu b t := by
    intro b hb t
    exact div_nonneg (hg b hb t) (le_of_lt (hpos b hb))
  have hmu_support : ∀ b ∈ z, ∀ t, t ∉ T → mu b t = 0 := by
    intro b hb t ht
    dsimp [mu]
    rw [hsupport b hb t ht, zero_div]
  have hmu_prob : ∀ b ∈ z, (∑ t ∈ T, mu b t) = 1 := by
    intro b hb
    exact normalized_row_mass T (g b) (hpos b hb)
  have hcap : ∀ b ∈ z, (∑ j ∈ i, ∑ x ∈ K, (v j b x) ^ 2) ≤
      1 + ((∑ j ∈ i, ((F j).card : ℝ)) - 1) * (∑ t ∈ T, (mu b t) ^ 2) := by
    intro b hb
    calc
      _ = ∑ j ∈ i, ∑ x ∈ K0, (∑ a ∈ F j, mu b (x - a)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact shifted_convolution_energy (F j) T K0 K (mu b) (c j b)
          (hmu_support b hb) (hK0 j hj) (hK j hj b hb)
      _ ≤ _ := actual_common_probe_capacity i F A T K0 D (mu b) hA hsub hdis
        hFD hTD hK0 hzero (hmu_nonneg b hb) (hmu_support b hb) (hmu_prob b hb)
  have hbound := ConditionalProbe.conditional_energy_capacity i z K T g v alpha
    ((∑ j ∈ i, ((F j).card : ℝ)) - 1) (sub_nonneg.mpr hsize)
    (fun b hb t ht => hg b hb t) halpha hpos hprob hcap
  calc
    _ = ∑ j ∈ i, ∑ x ∈ K, (∑ b ∈ z, W b * v j b x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      exact marginal_convolution z T (F j) g (c j) x hpos
    _ ≤ _ := hbound

end ShiftedMixture


namespace TupleFiberCode

theorem anchors_product_subset {I : Type*} [Fintype I] [DecidableEq I]
    (base : I) (U : I → Finset ℤ) (z : I → ℤ) :
    anchors base (Fintype.piFinset U) z ⊆ U base := by
  classical
  intro t ht
  obtain ⟨x, hx, hxt⟩ := Finset.mem_image.mp ht
  have hxp := (mem_fiber base (Fintype.piFinset U) x z).mp hx
  rw [← hxt]
  exact Fintype.mem_piFinset.mp hxp.1 base

theorem anchor_row_mass {I : Type*} [Fintype I] [DecidableEq I]
    (base : I) (U : I → Finset ℤ) (z : I → ℤ) :
    (∑ t ∈ U base, if t ∈ anchors base (Fintype.piFinset U) z then
      1 / ((Fintype.piFinset U).card : ℝ) else 0) =
      ((anchors base (Fintype.piFinset U) z).card : ℝ) /
        ((Fintype.piFinset U).card : ℝ) := by
  classical
  have hs := anchors_product_subset base U z
  have he : (∑ t ∈ anchors base (Fintype.piFinset U) z,
      if t ∈ anchors base (Fintype.piFinset U) z then
        1 / ((Fintype.piFinset U).card : ℝ) else 0) =
      ∑ t ∈ U base, if t ∈ anchors base (Fintype.piFinset U) z then
        1 / ((Fintype.piFinset U).card : ℝ) else 0 := by
    apply Finset.sum_subset hs
    intro t ht hn
    simp [hn]
  rw [← he]
  simp [div_eq_mul_inv]

theorem actual_uniform_product_capacity {I : Type*} [Fintype I] [DecidableEq I]
    (base : I) (F U : I → Finset ℤ) (A : Set ℤ) (K0 K D : Finset ℤ)
    (hU : ∀ j, (U j).Nonempty)
    (hA : SidonWeightedDifference.IsSidon A)
    (hsub : ∀ j, ∀ a ∈ F j, a ∈ A)
    (hdis : (Set.univ : Set I).PairwiseDisjoint F)
    (hFD : ∀ j, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ U base, ∀ u ∈ U base, u - t ∈ D)
    (hK0 : ∀ j, ∀ a ∈ F j, ∀ t ∈ U base, t + a ∈ K0)
    (hK : ∀ j, ∀ z ∈ patterns base (Fintype.piFinset U), ∀ x ∈ K0, x + z j ∈ K)
    (hzero : 0 ∈ D)
    (hsize : 1 ≤ ∑ j, ((F j).card : ℝ)) :
    (∑ j, ∑ x ∈ K,
      (∑ a ∈ F j, if x - a ∈ U j then 1 / ((U j).card : ℝ) else 0) ^ 2) ≤
      1 + ((∑ j, ((F j).card : ℝ)) - 1) *
        (((patterns base (Fintype.piFinset U)).card : ℝ) /
          ((Fintype.piFinset U).card : ℝ)) := by
  classical
  let omega := Fintype.piFinset U
  let Z := patterns base omega
  let g := fun z t => if t ∈ anchors base omega z then 1 / (omega.card : ℝ) else 0
  have homega : omega.Nonempty := Fintype.piFinset_nonempty.mpr hU
  have hP : (0 : ℝ) < omega.card := by exact_mod_cast Finset.card_pos.mpr homega
  have hg : ∀ z ∈ Z, ∀ t, 0 ≤ g z t := by
    intro z hz t
    dsimp [g]
    split_ifs
    · exact div_nonneg zero_le_one (le_of_lt hP)
    · exact le_refl 0
  have hs : ∀ z ∈ Z, ∀ t, t ∉ U base → g z t = 0 := by
    intro z hz t ht
    dsimp [g]
    exact if_neg (fun ha => ht (anchors_product_subset base U z ha))
  have ha : ∀ z ∈ Z, ∀ t ∈ U base, g z t ≤ 1 / (omega.card : ℝ) := by
    intro z hz t ht
    dsimp [g]
    split_ifs
    · exact le_refl _
    · exact div_nonneg zero_le_one (le_of_lt hP)
  have hr : ∀ z, (∑ t ∈ U base, g z t) =
      ((anchors base omega z).card : ℝ) / (omega.card : ℝ) :=
    fun z => anchor_row_mass base U z
  have hp : ∀ z ∈ Z, 0 < ∑ t ∈ U base, g z t := by
    intro z hz
    rw [hr]
    have hn : (0 : ℝ) < (anchors base omega z).card := by
      exact_mod_cast Finset.card_pos.mpr (anchors_nonempty base omega z hz)
    exact div_pos hn hP
  have hprob : (∑ z ∈ Z, ∑ t ∈ U base, g z t) = 1 := by
    simp_rw [hr]
    exact uniform_row_mass_total base omega homega
  have hcap := ShiftedMixture.actual_shifted_mixture_capacity
    Finset.univ Z F A (U base) K0 K D g (fun j z => z j) (1 / (omega.card : ℝ))
    hA (fun j hj => hsub j) (by simpa using hdis) (fun j hj => hFD j) hTD
    (fun j hj => hK0 j) (fun j hj => hK j) hzero hg hs ha hp hprob hsize
  have hm : ∀ j u, (∑ z ∈ Z, g z (u - z j)) =
      if u ∈ U j then 1 / ((U j).card : ℝ) else 0 := by
    intro j u
    exact product_shifted_uniform base U hU j u
  simp_rw [hm] at hcap
  simpa only [div_eq_mul_inv, one_mul] using hcap

end TupleFiberCode


open TupleFiberCode

theorem result {I : Type*} [Fintype I] [DecidableEq I]
    (base : I) (F U : I → Finset ℤ) (A : Set ℤ) (K0 K D : Finset ℤ)
    (hU : ∀ j, (U j).Nonempty)
    (hA : SidonWeightedDifference.IsSidon A)
    (hsub : ∀ j, ∀ a ∈ F j, a ∈ A)
    (hdis : (Set.univ : Set I).PairwiseDisjoint F)
    (hFD : ∀ j, ∀ a ∈ F j, ∀ b ∈ F j, a - b ∈ D)
    (hTD : ∀ t ∈ U base, ∀ u ∈ U base, u - t ∈ D)
    (hK0 : ∀ j, ∀ a ∈ F j, ∀ t ∈ U base, t + a ∈ K0)
    (hK : ∀ j, ∀ z ∈ patterns base (Fintype.piFinset U), ∀ x ∈ K0, x + z j ∈ K)
    (hzero : 0 ∈ D)
    (hsize : 1 ≤ ∑ j, ((F j).card : ℝ)) :
    (∑ j, ∑ x ∈ K,
      (∑ a ∈ F j, if x - a ∈ U j then 1 / ((U j).card : ℝ) else 0) ^ 2) ≤
      1 + ((∑ j, ((F j).card : ℝ)) - 1) *
        (((patterns base (Fintype.piFinset U)).card : ℝ) /
          ((Fintype.piFinset U).card : ℝ)) :=
  TupleFiberCode.actual_uniform_product_capacity base F U A K0 K D
    hU hA hsub hdis hFD hTD hK0 hK hzero hsize

end Submissions.J6P280UniformProductCapacity.Main
