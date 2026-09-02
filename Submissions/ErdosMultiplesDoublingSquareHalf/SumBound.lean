import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
The Square Bound for `A ⊆ (n/2, n]`.

* `M(n) = |A|`: the only multiple of `a` in `[1, n]` is `a` itself (`a·t ≤ n < 2a` forces
  `t = 1`), so `U(n) = n − r`, `r = |A|`.
* Union bound: `M(m) ≤ ∑_{a∈A} ⌊m/a⌋ ≤ m ∑_{a∈A} 1/a`.
* Sum bound (`sum_inv_le`, induction on the maximum): for `r` distinct integers in `(n/2, n]`,
  `∑ 1/a ≤ r(2n − r)/n²`. The maximum `a` of a set of `r' + 1` such integers satisfies
  `a ≥ ⌊n/2⌋ + r' + 1`, so `1/a ≤ 2/(n + 2r' + 1)`, and
  `2/(n + 2r' + 1) ≤ (2n − 2r' − 1)/n²` because `(2r'+1)(n − 2r') ≥ 1` when `n ≥ 2r' + 1`.
* Hence `M(m) n² ≤ m r (2n − r) = m (n² − (n−r)²)`, i.e. `(n − r)² m ≤ (m − M(m)) n²`.
-/

namespace Submissions.ErdosMultiplesDoublingSquareHalf.SumBound

open Finset

lemma card_mult (a x : ℕ) : ((Icc 1 x).filter (fun k => a ∣ k)).card = x / a := by
  have : (Icc 1 x) = Ioc 0 x := by
    have h := Icc_add_one_left_eq_Ioc (0 : ℕ) x
    simpa using h
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma card_le_sum (A : Finset ℕ) (x : ℕ) :
    ((Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤ ∑ a ∈ A, x / a := by
  have hsub : (Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k) ⊆
      A.biUnion (fun a => (Icc 1 x).filter (fun k => a ∣ k)) := by
    intro k hk
    simp only [mem_filter, mem_biUnion] at hk ⊢
    obtain ⟨hk1, a, ha, hak⟩ := hk
    exact ⟨a, ha, hk1, hak⟩
  calc ((Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card
      ≤ (A.biUnion (fun a => (Icc 1 x).filter (fun k => a ∣ k))).card := card_le_card hsub
    _ ≤ ∑ a ∈ A, ((Icc 1 x).filter (fun k => a ∣ k)).card := card_biUnion_le
    _ = ∑ a ∈ A, x / a := by simp only [card_mult]

lemma natdiv_le_ratdiv (x a : ℕ) : ((x / a : ℕ) : ℚ) ≤ (x : ℚ) / a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  · rw [le_div_iff₀ (by exact_mod_cast ha)]
    exact_mod_cast Nat.div_mul_le_self x a

lemma card_nonmult (A : Finset ℕ) (x : ℕ) :
    ((Icc 1 x).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card =
      x - ((Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  have := Finset.card_filter_add_card_filter_not (s := Icc 1 x) (fun k => ∃ a ∈ A, a ∣ k)
  rw [Nat.card_Icc] at this
  omega

/-- In the half range, the multiples of `A` in `[1, n]` are exactly the elements of `A`. -/
lemma filter_eq_self (A : Finset ℕ) (n : ℕ) (h0 : 0 ∉ A) (hA : ∀ a ∈ A, a ≤ n ∧ n < 2 * a) :
    (Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k) = A := by
  ext k
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hk1, hkn⟩, a, ha, t, rfl⟩
    obtain ⟨han, hn2⟩ := hA a ha
    have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
    have ht : t = 1 := by
      rcases Nat.lt_or_ge t 2 with h | h
      · have ht0 : t ≠ 0 := by
          rintro rfl
          simp at hk1
        omega
      · nlinarith
    rw [ht, mul_one]; exact ha
  · intro hk
    obtain ⟨hkn, _⟩ := hA k hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hk))
    exact ⟨⟨hk0, hkn⟩, k, hk, dvd_refl k⟩

/-- `∑_{a∈A} 1/a ≤ r(2n − r)/n²` for `A ⊆ (n/2, n]`, `r = |A|`. -/
lemma sum_inv_le (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ n ∧ n < 2 * a) :
    ∑ a ∈ A, (1 : ℚ) / a ≤ (A.card : ℚ) * (2 * n - A.card) / (n : ℚ) ^ 2 := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have hnot : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs : ∀ x ∈ s, x ≤ n ∧ n < 2 * x := fun x hx => hA x (mem_insert_of_mem hx)
    have ih' := ih hs
    obtain ⟨han, hn2⟩ := hA a (mem_insert_self a s)
    -- `insert a s ⊆ Icc (n/2 + 1) a`, so `s.card + 1 ≤ a - n/2`.
    have hsub : insert a s ⊆ Icc (n / 2 + 1) a := by
      intro x hx
      rw [mem_Icc]
      rcases mem_insert.mp hx with rfl | hxs
      · constructor
        · omega
        · exact le_refl _
      · obtain ⟨_, hx2⟩ := hs x hxs
        exact ⟨by omega, le_of_lt (hlt x hxs)⟩
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hnot, Nat.card_Icc] at hcard
    have ha2 : n + 2 * s.card + 1 ≤ 2 * a := by omega
    have hnr : 2 * s.card + 1 ≤ n := by omega
    rw [sum_insert hnot, card_insert_of_notMem hnot]
    set r := s.card with hr
    have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
    have ha0 : (0 : ℚ) < a := by exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos _) (by omega : 1 ≤ a))
    have ha2' : (n : ℚ) + 2 * r + 1 ≤ 2 * a := by exact_mod_cast ha2
    have hnr' : 2 * (r : ℚ) + 1 ≤ n := by exact_mod_cast hnr
    have hr0 : (0 : ℚ) ≤ r := by positivity
    have h1 : (1 : ℚ) / a ≤ 2 / ((n : ℚ) + 2 * r + 1) := by
      rw [div_le_div_iff₀ ha0 (by positivity)]
      linarith
    have h2 : (2 : ℚ) / ((n : ℚ) + 2 * r + 1) ≤ (2 * n - 2 * r - 1) / (n : ℚ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ 2 * r + 1) (by linarith : (0:ℚ) ≤ n - 2 * r - 1)]
    have key : (1 : ℚ) / a + ∑ x ∈ s, (1 : ℚ) / x ≤
        (2 * n - 2 * r - 1) / (n : ℚ) ^ 2 + (r : ℚ) * (2 * n - r) / (n : ℚ) ^ 2 := by
      linarith
    push_cast
    calc (1 : ℚ) / a + ∑ x ∈ s, (1 : ℚ) / x
        ≤ (2 * n - 2 * r - 1) / (n : ℚ) ^ 2 + (r : ℚ) * (2 * n - r) / (n : ℚ) ^ 2 := key
      _ = ((r : ℚ) + 1) * (2 * n - ((r : ℚ) + 1)) / (n : ℚ) ^ 2 := by ring

theorem proof : ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n ∧ n < 2 * a) → n < m →
      ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * m ≤
        ((Finset.Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card * n ^ 2 := by
  intro A hA h0 n m hAn hnm
  obtain ⟨a, ha⟩ := hA
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
  have hn : 0 < n := lt_of_lt_of_le ha0 (hAn a ha).1
  rw [card_nonmult, card_nonmult, filter_eq_self A n h0 hAn]
  set r := A.card with hr
  set Mm := ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card with hMm
  have hrn : r ≤ n := by
    have := card_le_card (show A ⊆ Icc 1 n from fun x hx => by
      rw [mem_Icc]; exact ⟨Nat.pos_of_ne_zero (fun h => h0 (h ▸ hx)), (hAn x hx).1⟩)
    rw [Nat.card_Icc] at this; omega
  have hMmm : Mm ≤ m := by
    have := card_le_card (filter_subset (fun k => ∃ a ∈ A, a ∣ k) (Icc 1 m))
    rw [Nat.card_Icc] at this; omega
  -- union bound in ℚ
  have hsum := sum_inv_le n hn A hAn
  have h1 : (Mm : ℚ) ≤ (m : ℚ) * ((r : ℚ) * (2 * n - r) / (n : ℚ) ^ 2) := by
    calc (Mm : ℚ) ≤ ((∑ a ∈ A, m / a : ℕ) : ℚ) := by exact_mod_cast card_le_sum A m
      _ = ∑ a ∈ A, ((m / a : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ ∑ a ∈ A, (m : ℚ) / a := sum_le_sum (fun a _ => natdiv_le_ratdiv m a)
      _ = (m : ℚ) * ∑ a ∈ A, (1 : ℚ) / a := by
          rw [mul_sum]; refine sum_congr rfl (fun a _ => ?_); ring
      _ ≤ (m : ℚ) * ((r : ℚ) * (2 * n - r) / (n : ℚ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
  have h2 : (Mm : ℚ) * (n : ℚ) ^ 2 ≤ (m : ℚ) * ((r : ℚ) * (2 * n - r)) := by
    have := mul_le_mul_of_nonneg_right h1 (le_of_lt (pow_pos hn0 2))
    calc (Mm : ℚ) * (n : ℚ) ^ 2 ≤ (m : ℚ) * ((r : ℚ) * (2 * n - r) / (n : ℚ) ^ 2) * (n : ℚ) ^ 2 := this
      _ = (m : ℚ) * ((r : ℚ) * (2 * n - r)) := by field_simp
  have goal : ((n - r : ℕ) : ℚ) ^ 2 * m ≤ ((m - Mm : ℕ) : ℚ) * (n : ℚ) ^ 2 := by
    rw [Nat.cast_sub hrn, Nat.cast_sub hMmm]
    nlinarith [h2]
  exact_mod_cast goal

end Submissions.ErdosMultiplesDoublingSquareHalf.SumBound
