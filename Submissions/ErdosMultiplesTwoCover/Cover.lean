import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith

namespace Submissions.ErdosMultiplesTwoCover.Cover

open Finset

def multiples (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)

lemma card_mult (a x : ℕ) : ((Icc 1 x).filter (fun k => a ∣ k)).card = x / a := by
  have h : (Icc 1 x) = Ioc 0 x := by
    simpa using Icc_add_one_left_eq_Ioc (0 : ℕ) x
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

lemma single_bound (a n m : ℕ) (ha : 0 < a) (han : a ≤ n) (hnm : n < m) :
    n * (m / a) < 2 * m * (n / a) := by
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have hn : n < (n / a + 1) * a := by
    simpa [Nat.add_mul] using (Nat.lt_div_mul_add (a := n) ha)
  have hn' : n < 2 * a * (n / a) := by nlinarith
  have hm : a * (m / a) ≤ m := Nat.mul_div_le m a
  have h1 := Nat.mul_le_mul_left n hm
  have h2 := Nat.mul_lt_mul_of_pos_right hn' (show 0 < m by omega)
  have h3 : a * (n * (m / a)) < a * (2 * m * (n / a)) := by nlinarith
  exact Nat.lt_of_mul_lt_mul_left h3

/-- A present generator a and a second covering modulus b >= a suffice, even
when b is absent from A and A has arbitrarily many primitive generators. -/
theorem proof : ∀ A : Finset ℕ, 0 ∉ A → ∀ a b : ℕ, a ∈ A → a ≤ b →
    (∀ c ∈ A, a ∣ c ∨ b ∣ c) → ∀ n m : ℕ,
    (∀ c ∈ A, c ≤ n) → n < m →
    n * ((Icc 1 m).filter (fun k => ∃ c ∈ A, c ∣ k)).card <
      2 * m * ((Icc 1 n).filter (fun k => ∃ c ∈ A, c ∣ k)).card := by
  intro A hzero a b ha hab hcover n m hmax hnm
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => hzero (h ▸ ha))
  have han : a ≤ n := hmax a ha
  have hm0 : 0 < m := by omega
  change n * (multiples A m).card < 2 * m * (multiples A n).card
  by_cases hall : ∀ c ∈ A, a ∣ c
  · have heq (x : ℕ) : multiples A x = (Icc 1 x).filter (fun k => a ∣ k) := by
      ext k
      simp only [multiples, mem_filter]
      constructor
      · rintro ⟨hk, c, hc, hck⟩
        exact ⟨hk, dvd_trans (hall c hc) hck⟩
      · rintro ⟨hk, hak⟩
        exact ⟨hk, a, ha, hak⟩
    rw [heq, heq, card_mult, card_mult]
    exact single_bound a n m ha0 han hnm
  · push Not at hall
    obtain ⟨c, hc, hnc⟩ := hall
    have hc0 : 0 < c := Nat.pos_of_ne_zero (fun h => hzero (h ▸ hc))
    have hcn : c ≤ n := hmax c hc
    have hsub : insert c ((Icc 1 n).filter (fun k => a ∣ k)) ⊆ multiples A n := by
      intro k hk
      rcases mem_insert.mp hk with hkc | hk
      · subst k
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hc0, hcn⟩, c, hc, dvd_refl c⟩
      · obtain ⟨hk, hd⟩ := mem_filter.mp hk
        exact mem_filter.mpr ⟨hk, a, ha, hd⟩
    have hnot : c ∉ (Icc 1 n).filter (fun k => a ∣ k) := by simp [hnc]
    have hlower := card_le_card hsub
    rw [card_insert_of_notMem hnot, card_mult] at hlower
    have hround : n < (n / a + 1) * a := by
      simpa [Nat.add_mul] using (Nat.lt_div_mul_add (a := n) ha0)
    have hnear : n < a * (multiples A n).card := by nlinarith
    have hupper : multiples A m ⊆
        (Icc 1 m).filter (fun k => a ∣ k) ∪ (Icc 1 m).filter (fun k => b ∣ k) := by
      intro k hk
      obtain ⟨hk, c, hc, hck⟩ := mem_filter.mp hk
      rcases hcover c hc with hac | hbc
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hk, dvd_trans hac hck⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hk, dvd_trans hbc hck⟩))
    have hcard : (multiples A m).card ≤ m / a + m / b := by
      calc (multiples A m).card ≤ _ := card_le_card hupper
        _ ≤ _ := card_union_le _ _
        _ = _ := by rw [card_mult, card_mult]
    have hbdiv := Nat.mul_div_le m b
    have hadiv := Nat.mul_div_le m a
    have hmono := Nat.mul_le_mul_right (m / b) hab
    have hfar : a * (multiples A m).card ≤ 2 * m := by nlinarith
    have h1 := Nat.mul_le_mul_left n hfar
    have h2 := Nat.mul_lt_mul_of_pos_right hnear (show 0 < 2 * m by omega)
    have h3 : a * (n * (multiples A m).card) < a * (2 * m * (multiples A n).card) := by
      nlinarith
    exact Nat.lt_of_mul_lt_mul_left h3

/-- A nontrivial example; the covering modulus 4 is absent from A. -/
theorem example_hypotheses :
    0 ∉ ({3,20,28,44,52} : Finset ℕ) ∧ 3 ∈ ({3,20,28,44,52} : Finset ℕ) ∧
    3 ≤ (4 : ℕ) ∧ (∀ c ∈ ({3,20,28,44,52} : Finset ℕ), 3 ∣ c ∨ 4 ∣ c) := by decide

end Submissions.ErdosMultiplesTwoCover.Cover
