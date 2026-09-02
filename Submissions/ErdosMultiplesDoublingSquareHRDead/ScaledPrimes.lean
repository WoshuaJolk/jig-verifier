import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The finite Heilbronn–Rohrbach bound `U(n)² ≤ n² ∏_{a∈A}(1 − 1/a)` fails.

Witness `A = 52 · S`, `S = {primes ≤ 67}`, `n = 52 · 199 = 10348`. For a scaled set the
multiples of `c·S` in `[1, cN]` are exactly `c` times the multiples of `S` in `[1, N]`
(`scaled_filter`), so `M_A(n) = M_S(199) = 171` (one `decide` on a `199 × 19` table) and
`U(n) = 10348 − 171 = 10177`. The remaining inequality
`10348² ∏ (52p − 1) < 10177² ∏ 52p` is a closed numeral comparison.
-/

namespace Submissions.ErdosMultiplesDoublingSquareHRDead.ScaledPrimes

open Finset

abbrev S : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67}

lemma scaled_filter (S : Finset ℕ) (c N : ℕ) (hc : 0 < c) :
    (Icc 1 (c * N)).filter (fun k => ∃ a ∈ S.image (fun s => c * s), a ∣ k) =
      ((Icc 1 N).filter (fun t => ∃ s ∈ S, s ∣ t)).image (fun t => c * t) := by
  ext k
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨hk1, hkN⟩, a, ha, hak⟩
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨u, rfl⟩ := hak
    have e : c * s * u = c * (s * u) := by ring
    rw [e] at hk1 hkN
    refine ⟨s * u, ⟨⟨?_, Nat.le_of_mul_le_mul_left hkN hc⟩, s, hs, dvd_mul_right s u⟩, e.symm⟩
    rcases Nat.eq_zero_or_pos (s * u) with h | h
    · rw [h] at hk1; simp at hk1
    · exact h
  · rintro ⟨t, ⟨⟨ht1, htN⟩, s, hs, hst⟩, rfl⟩
    exact ⟨⟨by nlinarith, Nat.mul_le_mul_left c htN⟩, c * s, ⟨s, hs, rfl⟩,
      Nat.mul_dvd_mul_left c hst⟩

lemma card_scaled (S : Finset ℕ) (c N : ℕ) (hc : 0 < c) :
    ((Icc 1 (c * N)).filter (fun k => ∃ a ∈ S.image (fun s => c * s), a ∣ k)).card =
      ((Icc 1 N).filter (fun t => ∃ s ∈ S, s ∣ t)).card := by
  rw [scaled_filter S c N hc]
  apply card_image_of_injective
  intro x y hxy
  exact Nat.eq_of_mul_eq_mul_left hc hxy

lemma card_nonmult (A : Finset ℕ) (x : ℕ) :
    ((Icc 1 x).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card =
      x - ((Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  have := Finset.card_filter_add_card_filter_not (s := Icc 1 x) (fun k => ∃ a ∈ A, a ∣ k)
  rw [Nat.card_Icc] at this
  omega

lemma MS : ((Icc 1 199).filter (fun t => ∃ s ∈ S, s ∣ t)).card = 171 := by decide +kernel

theorem proof :
    ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
      ∃ n : ℕ, (∀ a ∈ A, a ≤ n) ∧
        n ^ 2 * (∏ a ∈ A, (a - 1)) <
          ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * (∏ a ∈ A, a) := by
  refine ⟨S.image (fun s => 52 * s), by decide, by decide, 52 * 199, by decide, ?_⟩
  rw [card_nonmult, card_scaled S 52 199 (by norm_num), MS]
  decide

end Submissions.ErdosMultiplesDoublingSquareHRDead.ScaledPrimes
