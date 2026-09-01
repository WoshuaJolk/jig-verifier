import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
Let `S1 = {k ≤ n : exactly one of a, b, c divides k}` and `S3 = {k ≤ n : a, b, c all divide k}`.
Double counting gives `n/a + n/b + n/c + #S3 = 2 * M n - ... `, precisely
`2 * M n + #S3 = (n/a + n/b + n/c) + #S1`, so the claim is `#S3 + 3 ≤ #S1`.
`S1` contains `a, b, c` (primitivity) and the image of the injection
`φ(k) = k - c` (or `2a` when `k = 2c`) on `S3`: `c ∣ k - c`, while `a ∣ k - c` would force
`a ∣ c`; the image avoids `{a, b, c}` because `k - c ≥ 2c` once `k ≠ 2c`.
-/

namespace Submissions.ErdosMultiplesDoublingThree.ViaCriterion

open Finset

lemma card_mult (a x : ℕ) : ((Icc 1 x).filter (fun k => a ∣ k)).card = x / a := by
  have : (Icc 1 x) = Ioc 0 x := by
    have h := Icc_add_one_left_eq_Ioc (0 : ℕ) x
    simpa using h
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

/-- `b ∤ 2a` for `a < b` unless `a ∣ b`. -/
lemma not_dvd_two_mul {a b : ℕ} (ha : 0 < a) (hab : a < b) (hnd : ¬ a ∣ b) : ¬ b ∣ 2 * a := by
  rintro ⟨j, hj⟩
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · omega
    · exact hnd ⟨2, by omega⟩
  · have : b * 2 ≤ b * j := Nat.mul_le_mul_left b hj2
    omega

section

variable {a b c n : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
  (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnbc : ¬ b ∣ c) (hcn : c ≤ n)

/-- Exactly one of `a, b, c` divides `k`. -/
def one (a b c k : ℕ) : Prop :=
  (a ∣ k ∧ ¬ b ∣ k ∧ ¬ c ∣ k) ∨ (¬ a ∣ k ∧ b ∣ k ∧ ¬ c ∣ k) ∨ (¬ a ∣ k ∧ ¬ b ∣ k ∧ c ∣ k)

/-- All three divide `k`. -/
def three (a b c k : ℕ) : Prop := a ∣ k ∧ b ∣ k ∧ c ∣ k

instance (a b c k : ℕ) : Decidable (one a b c k) := by unfold one; infer_instance
instance (a b c k : ℕ) : Decidable (three a b c k) := by unfold three; infer_instance

lemma pointwise (k : ℕ) :
    2 * (if a ∣ k ∨ b ∣ k ∨ c ∣ k then 1 else 0) + (if three a b c k then 1 else 0) =
      ((if a ∣ k then 1 else 0) + (if b ∣ k then 1 else 0) + (if c ∣ k then 1 else 0)) +
        (if one a b c k then 1 else 0) := by
  unfold one three
  by_cases h1 : a ∣ k <;> by_cases h2 : b ∣ k <;> by_cases h3 : c ∣ k <;> simp [h1, h2, h3]

lemma sum_identity :
    2 * ((Icc 1 n).filter (fun k => a ∣ k ∨ b ∣ k ∨ c ∣ k)).card +
        ((Icc 1 n).filter (fun k => three a b c k)).card =
      (n / a + n / b + n / c) + ((Icc 1 n).filter (fun k => one a b c k)).card := by
  rw [← card_mult a n, ← card_mult b n, ← card_mult c n]
  simp only [card_filter]
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl (fun k _ => pointwise k)

include ha hab hbc hnab hnac hnbc hcn in
lemma abc_subset :
    ({a, b, c} : Finset ℕ) ⊆ (Icc 1 n).filter (fun k => one a b c k) := by
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  simp only [mem_filter, mem_Icc]
  rcases hx with rfl | rfl | rfl
  · refine ⟨⟨ha, by omega⟩, Or.inl ⟨dvd_refl _, ?_, ?_⟩⟩
    · exact fun h => absurd (Nat.le_of_dvd ha h) (by omega)
    · exact fun h => absurd (Nat.le_of_dvd ha h) (by omega)
  · refine ⟨⟨by omega, by omega⟩, Or.inr (Or.inl ⟨hnab, dvd_refl _, ?_⟩)⟩
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  · exact ⟨⟨by omega, hcn⟩, Or.inr (Or.inr ⟨hnac, hnbc, dvd_refl _⟩)⟩

/-- The injection `S3 → S1 \ {a,b,c}`. -/
def φ (a c k : ℕ) : ℕ := if k = 2 * c then 2 * a else k - c

include ha hab hbc hnab hnac hnbc in
lemma phi_mem {k : ℕ} (hk : k ∈ (Icc 1 n).filter (fun k => three a b c k)) :
    φ a c k ∈ (Icc 1 n).filter (fun k => one a b c k) ∧ φ a c k ∉ ({a, b, c} : Finset ℕ) := by
  rw [mem_filter, mem_Icc] at hk
  unfold three at hk
  obtain ⟨⟨hk1, hkn⟩, hak, hbk, hck⟩ := hk
  have hck' : c ≤ k := Nat.le_of_dvd (by omega) hck
  -- `k ≠ c` since `a ∣ k` and `a ∤ c`
  have hkc : k ≠ c := fun h => hnac (h ▸ hak)
  -- `k ≥ 2c`
  have hk2 : 2 * c ≤ k := by
    obtain ⟨t, ht⟩ := hck
    rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t <;> omega
    · have := Nat.mul_le_mul_left c h; omega
  rw [mem_filter, mem_Icc, mem_insert, mem_insert, mem_singleton]
  unfold φ
  split_ifs with h2c
  · -- k = 2c: witness 2a
    have hb2a : ¬ b ∣ 2 * a := not_dvd_two_mul ha hab hnab
    have hc2a : ¬ c ∣ 2 * a := not_dvd_two_mul ha (by omega) hnac
    refine ⟨⟨⟨by omega, by omega⟩, Or.inl ⟨⟨2, by ring⟩, hb2a, hc2a⟩⟩, ?_⟩
    simp only [not_or]
    refine ⟨by omega, fun h => hnab ⟨2, by omega⟩, fun h => hnac ⟨2, by omega⟩⟩
  · -- k ≥ 3c: witness k - c
    have hk3 : 3 * c ≤ k := by
      obtain ⟨t, ht⟩ := hck
      rcases Nat.lt_or_ge t 3 with h | h
      · interval_cases t <;> omega
      · have := Nat.mul_le_mul_left c h; omega
    have hcd : c ∣ k - c := Nat.dvd_sub hck (dvd_refl c)
    have hna : ¬ a ∣ k - c := by
      intro h
      have := Nat.dvd_sub hak h
      rw [Nat.sub_sub_self hck'] at this
      exact hnac this
    have hnb : ¬ b ∣ k - c := by
      intro h
      have := Nat.dvd_sub hbk h
      rw [Nat.sub_sub_self hck'] at this
      exact hnbc this
    refine ⟨⟨⟨by omega, by omega⟩, Or.inr (Or.inr ⟨hna, hnb, hcd⟩)⟩, ?_⟩
    simp only [not_or]
    omega

include hab hbc hnac in
lemma phi_injOn :
    Set.InjOn (φ a c) ((Icc 1 n).filter (fun k => three a b c k) : Set ℕ) := by
  intro k hk k' hk' heq
  rw [mem_coe, mem_filter, mem_Icc] at hk hk'
  unfold three at hk hk'
  have hck : c ≤ k := Nat.le_of_dvd (by omega) hk.2.2.2
  have hck' : c ≤ k' := Nat.le_of_dvd (by omega) hk'.2.2.2
  have h3 : ∀ j, 1 ≤ j → c ∣ j → j ≠ 2 * c → a ∣ j → 3 * c ≤ j := by
    intro j hj1 hcj hj2 haj
    obtain ⟨t, ht⟩ := hcj
    have hjc : j ≠ c := fun h => hnac (h ▸ haj)
    rcases Nat.lt_or_ge t 3 with h | h
    · interval_cases t <;> omega
    · have := Nat.mul_le_mul_left c h; omega
  unfold φ at heq
  split_ifs at heq with h1 h2 h2
  · omega
  · have := h3 k' hk'.1.1 hk'.2.2.2 h2 hk'.2.1
    omega
  · have := h3 k hk.1.1 hk.2.2.2 h1 hk.2.1
    omega
  · omega

end

theorem criterion : ∀ a b c : ℕ, 0 < a → a < b → b < c → ¬ a ∣ b → ¬ a ∣ c → ¬ b ∣ c →
    ∀ n : ℕ, c ≤ n →
    n / a + n / b + n / c + 3 ≤
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k)).card := by
  intro a b c ha hab hbc hnab hnac hnbc n hcn
  have hfilt : (Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k) =
      (Icc 1 n).filter (fun k => a ∣ k ∨ b ∣ k ∨ c ∣ k) := by
    apply filter_congr
    intro k _
    simp [mem_insert, mem_singleton, or_and_right, exists_or]
  rw [hfilt]
  have hid := sum_identity (a := a) (b := b) (c := c) (n := n)
  -- #S1 ≥ 3 + #S3 via {a,b,c} ⊔ φ(S3) ⊆ S1
  set S1 := (Icc 1 n).filter (fun k => one a b c k) with hS1
  set S3 := (Icc 1 n).filter (fun k => three a b c k) with hS3
  have hsub : ({a, b, c} : Finset ℕ) ∪ S3.image (φ a c) ⊆ S1 := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · exact abc_subset ha hab hbc hnab hnac hnbc hcn h
    · obtain ⟨k, hk, rfl⟩ := mem_image.mp h
      exact (phi_mem ha hab hbc hnab hnac hnbc hk).1
  have hdisj : Disjoint ({a, b, c} : Finset ℕ) (S3.image (φ a c)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx'
    exact (phi_mem ha hab hbc hnab hnac hnbc hk).2 hx
  have hcard3 : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp; omega
    · simp only [mem_insert, mem_singleton, not_or]; omega
  have himg : (S3.image (φ a c)).card = S3.card :=
    card_image_of_injOn (phi_injOn hab hbc hnac)
  have h1 : 3 + S3.card ≤ S1.card := by
    calc 3 + S3.card = (({a, b, c} : Finset ℕ) ∪ S3.image (φ a c)).card := by
          rw [card_union_of_disjoint hdisj, hcard3, himg]
      _ ≤ S1.card := card_le_card hsub
  omega

lemma card_le_three (a b c x : ℕ) :
    ((Icc 1 x).filter (fun k => ∃ y ∈ ({a, b, c} : Finset ℕ), y ∣ k)).card ≤
      x / a + x / b + x / c := by
  have hfilt : (Icc 1 x).filter (fun k => ∃ y ∈ ({a, b, c} : Finset ℕ), y ∣ k) =
      (Icc 1 x).filter (fun k => a ∣ k) ∪ (Icc 1 x).filter (fun k => b ∣ k) ∪
        (Icc 1 x).filter (fun k => c ∣ k) := by
    rw [← filter_or, ← filter_or]
    apply filter_congr
    intro k _
    simp [mem_insert, mem_singleton, or_and_right, exists_or, or_assoc]
  rw [hfilt, ← card_mult a x, ← card_mult b x, ← card_mult c x]
  exact le_trans (card_union_le _ _) (Nat.add_le_add_right (card_union_le _ _) _)

lemma cross (n m x : ℕ) (hx : 0 < x) (hm : 0 < m) : n * (m / x) < m * (n / x + 1) := by
  have h1 : x * (n * (m / x)) ≤ n * m := by
    rw [mul_left_comm]
    exact Nat.mul_le_mul_left n (Nat.mul_div_le m x)
  have h2 : n * m < x * (m * (n / x + 1)) := by
    rw [mul_left_comm, mul_comm n m]
    exact Nat.mul_lt_mul_of_pos_left (Nat.lt_mul_div_succ n hx) hm
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 h2)

theorem proof : ∀ a b c : ℕ, 0 < a → a < b → b < c → ¬ a ∣ b → ¬ a ∣ c → ¬ b ∣ c →
    ∀ n m : ℕ, c ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k)).card := by
  intro a b c ha hab hbc hnab hnac hnbc n m hcn hnm
  have hcrit := criterion a b c ha hab hbc hnab hnac hnbc n hcn
  have hMm := card_le_three a b c m
  set Mm := ((Finset.Icc 1 m).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k)).card
  set Mn := ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k)).card
  have hm : 0 < m := by omega
  have h1 : n * Mm ≤ n * (m / a + m / b + m / c) := Nat.mul_le_mul_left n hMm
  have ha' := cross n m a ha hm
  have hb' := cross n m b (by omega) hm
  have hc' := cross n m c (by omega) hm
  have h2 : m * (n / a + n / b + n / c + 3) ≤ m * (2 * Mn) := Nat.mul_le_mul_left m hcrit
  nlinarith [h1, ha', hb', hc', h2]

end Submissions.ErdosMultiplesDoublingThree.ViaCriterion
