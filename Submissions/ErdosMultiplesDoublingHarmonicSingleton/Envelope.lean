import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The Harmonic Bound for `A = {a}`: `⌊m/a⌋ (n + ⌊n/a⌋) ≤ 2m ⌊n/a⌋` for `1 ≤ a ≤ n < m`.

With `q = ⌊n/a⌋ ≥ 1` and `n < qa + a`: `n + q ≤ qa + (a − 1) + q ≤ 2qa` since
`(q − 1)(a − 1) ≥ 0`; then `⌊m/a⌋ (n + q) ≤ ⌊m/a⌋ · 2qa ≤ 2mq`.
-/

namespace Submissions.ErdosMultiplesDoublingHarmonicSingleton.Envelope

open Finset

lemma card_mult (a x : ℕ) :
    ((Icc 1 x).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card = x / a := by
  have h : ((Icc 1 x).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)) =
      (Ioc 0 x).filter (fun k => a ∣ k) := by
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    ext k
    simp
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

theorem proof : ∀ a : ℕ, 0 < a → ∀ n m : ℕ, a ≤ n → n < m →
    ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card *
        (n + ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card) ≤
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card := by
  intro a ha n m han hnm
  rw [card_mult, card_mult]
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have hn : n < n / a * a + a := Nat.lt_div_mul_add ha
  have hm : a * (m / a) ≤ m := Nat.mul_div_le m a
  set q := n / a with hq'
  set p := m / a with hp'
  have key : n + q ≤ 2 * q * a := by nlinarith
  calc p * (n + q) ≤ p * (2 * q * a) := Nat.mul_le_mul_left p key
    _ = 2 * q * (a * p) := by ring
    _ ≤ 2 * q * m := Nat.mul_le_mul_left _ hm
    _ = 2 * m * q := by ring

end Submissions.ErdosMultiplesDoublingHarmonicSingleton.Envelope
