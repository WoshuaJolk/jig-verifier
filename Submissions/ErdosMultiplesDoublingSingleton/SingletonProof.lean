import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The one-generator case of Erdős #488: `A = {a}`. Then `#{k ∈ [1,x] : a ∣ k} = x / a`, and
with `q = n / a ≥ 1` we have `n < a (q + 1) ≤ 2 a q`, so `a · n · (m / a) ≤ n m < 2 a q m`.
-/

namespace Submissions.ErdosMultiplesDoublingSingleton.SingletonProof

lemma card_filter_singleton (a x : ℕ) :
    ((Finset.Icc 1 x).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card = x / a := by
  have h : ((Finset.Icc 1 x).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)) =
      (Finset.Ioc 0 x).filter (fun k => a ∣ k) := by
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    ext k
    simp
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

theorem proof : ∀ a : ℕ, 0 < a → ∀ n m : ℕ, a ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card := by
  intro a ha n m han hnm
  rw [card_filter_singleton, card_filter_singleton]
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have h1 : n < a * (n / a + 1) := by
    have := Nat.lt_div_mul_add (a := n) ha
    rw [Nat.mul_comm] at this
    linarith [Nat.mul_succ a (n / a)]
  have h2 : a * (n / a + 1) ≤ 2 * a * (n / a) := by nlinarith
  have h3 : a * (m / a) ≤ m := Nat.mul_div_le m a
  have h4 : a * (n * (m / a)) ≤ n * m := by
    calc a * (n * (m / a)) = n * (a * (m / a)) := by ring
      _ ≤ n * m := Nat.mul_le_mul_left n h3
  have h5 : n * m < a * (2 * m * (n / a)) := by
    calc n * m < (2 * a * (n / a)) * m := Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le h1 h2)
            (lt_of_le_of_lt (Nat.zero_le n) hnm)
      _ = a * (2 * m * (n / a)) := by ring
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h4 h5)

end Submissions.ErdosMultiplesDoublingSingleton.SingletonProof
