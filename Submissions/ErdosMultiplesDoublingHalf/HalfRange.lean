import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
When every `a ∈ A` satisfies `n < 2a ≤ 2n`, the only multiple of `a` in `[1, n]` is `a`
itself, so `M n = |A|`, while `∑ a ∈ A, n / a < 2 |A|`. The union bound
`M m ≤ ∑ a ∈ A, m / a` then gives `n M m ≤ m ∑ n / a < 2 m M n`.
-/

namespace Submissions.ErdosMultiplesDoublingHalf.HalfRange

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

/-- In the half range, the multiples of `A` in `[1, n]` are exactly the elements of `A`. -/
lemma filter_eq_self (A : Finset ℕ) (n : ℕ) (hA : ∀ a ∈ A, n < 2 * a ∧ a ≤ n) :
    (Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k) = A := by
  ext k
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hk1, hkn⟩, a, ha, t, rfl⟩
    obtain ⟨h2a, han⟩ := hA a ha
    have ht : t = 1 := by
      rcases Nat.lt_or_ge t 2 with h | h
      · have : t ≠ 0 := by rintro rfl; simp at hk1
        omega
      · nlinarith
    subst ht
    simpa using ha
  · intro hk
    obtain ⟨h2a, han⟩ := hA k hk
    exact ⟨⟨by omega, han⟩, k, hk, dvd_refl k⟩

theorem proof : ∀ A : Finset ℕ, A.Nonempty → ∀ n m : ℕ, (∀ a ∈ A, n < 2 * a ∧ a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro A hne n m hA hnm
  rw [filter_eq_self A n hA]
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le n) hnm)
  have hsum : (∑ a ∈ A, (n : ℚ) / a) < 2 * (A.card : ℚ) := by
    have h : ∀ a ∈ A, (n : ℚ) / a < 2 := by
      intro a ha
      obtain ⟨h2a, _⟩ := hA a ha
      have ha0 : (0 : ℚ) < a := by
        have : 0 < a := by omega
        exact_mod_cast this
      rw [div_lt_iff₀ ha0]
      exact_mod_cast h2a
    calc (∑ a ∈ A, (n : ℚ) / a) < ∑ _a ∈ A, (2 : ℚ) := sum_lt_sum_of_nonempty hne h
      _ = 2 * (A.card : ℚ) := by rw [sum_const, nsmul_eq_mul, mul_comm]
  have h1 : (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card : ℚ) ≤
      ∑ a ∈ A, (m : ℚ) / a := by
    calc (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card : ℚ)
        ≤ ((∑ a ∈ A, m / a : ℕ) : ℚ) := by exact_mod_cast card_le_sum A m
      _ = ∑ a ∈ A, ((m / a : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ ∑ a ∈ A, (m : ℚ) / a := sum_le_sum (fun a _ => natdiv_le_ratdiv m a)
  have h2 : (n : ℚ) * ∑ a ∈ A, (m : ℚ) / a = m * ∑ a ∈ A, (n : ℚ) / a := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl (fun a _ => ?_)
    ring
  have h5 : (n : ℚ) * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card : ℚ) <
      2 * m * (A.card : ℚ) := by
    calc (n : ℚ) * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card : ℚ)
        ≤ n * ∑ a ∈ A, (m : ℚ) / a := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = m * ∑ a ∈ A, (n : ℚ) / a := h2
      _ < m * (2 * (A.card : ℚ)) := mul_lt_mul_of_pos_left hsum hm0
      _ = 2 * m * (A.card : ℚ) := by ring
  exact_mod_cast h5

end Submissions.ErdosMultiplesDoublingHalf.HalfRange
