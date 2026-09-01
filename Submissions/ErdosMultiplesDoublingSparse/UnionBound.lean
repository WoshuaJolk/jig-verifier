import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Union bound: `M m ≤ ∑ a ∈ A, m / a ≤ ∑ a ∈ A, (m : ℚ) / a = (m / n) * ∑ a ∈ A, (n : ℚ) / a`,
so `n * M m ≤ m * ∑ a ∈ A, n / a < 2 * m * M n`.
-/

namespace Submissions.ErdosMultiplesDoublingSparse.UnionBound

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

theorem proof : ∀ A : Finset ℕ, ∀ n m : ℕ, n < m →
    (∑ a ∈ A, (n : ℚ) / a) <
      2 * (((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card : ℚ) →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro A n m hnm hsum
  set Mm := ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card with hMm
  set Mn := ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card with hMn
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le n) hnm)
  have h1 : (Mm : ℚ) ≤ ∑ a ∈ A, (m : ℚ) / a := by
    calc (Mm : ℚ) ≤ ((∑ a ∈ A, m / a : ℕ) : ℚ) := by exact_mod_cast card_le_sum A m
      _ = ∑ a ∈ A, ((m / a : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ ∑ a ∈ A, (m : ℚ) / a := sum_le_sum (fun a _ => natdiv_le_ratdiv m a)
  have h2 : (n : ℚ) * ∑ a ∈ A, (m : ℚ) / a = m * ∑ a ∈ A, (n : ℚ) / a := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl (fun a _ => ?_)
    ring
  have h3 : (n : ℚ) * Mm ≤ m * ∑ a ∈ A, (n : ℚ) / a := by
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : (m : ℚ) * ∑ a ∈ A, (n : ℚ) / a < 2 * m * Mn := by
    have := mul_lt_mul_of_pos_left hsum hm0
    linarith
  have h5 : (n : ℚ) * Mm < 2 * m * Mn := lt_of_le_of_lt h3 h4
  exact_mod_cast h5

end Submissions.ErdosMultiplesDoublingSparse.UnionBound
