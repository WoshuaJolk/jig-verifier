import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
Square Bound ⇒ Erdős #488.

With `U(x) + M(x) = x` (complementary filters of `[1, x]`), the hypothesis
`U(n)² m ≤ U(m) n²` becomes `n² M(m) + m M(n)² ≤ 2nm M(n)`, and `M(n) ≥ 1`, `m ≥ 1` give the
strict `n · M(m) < 2m · M(n)` after cancelling `n > 0`.
-/

namespace Submissions.ErdosMultiplesDoublingSquareImplies.Complement

open Finset

lemma compl_add (A : Finset ℕ) (x : ℕ) :
    ((Icc 1 x).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card +
      ((Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card = x := by
  rw [add_comm, Finset.card_filter_add_card_filter_not, Nat.card_Icc]
  omega

theorem proof :
    (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * m ≤
          ((Finset.Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card * n ^ 2) →
    ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
          2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro SB A hA h0 n m hn hnm
  have h := SB A hA h0 n m hn hnm
  have hUn := compl_add A n
  have hUm := compl_add A m
  obtain ⟨a, ha⟩ := hA
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
  have hM : 1 ≤ ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
    apply Finset.card_pos.mpr
    exact ⟨a, by
      rw [mem_filter, mem_Icc]
      exact ⟨⟨ha0, hn a ha⟩, a, ha, dvd_refl a⟩⟩
  have hn0 : 0 < n := lt_of_lt_of_le ha0 (hn a ha)
  set Un := ((Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card
  set Um := ((Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card
  set Mn := ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card
  set Mm := ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card
  have key : n * (n * Mm) < n * (2 * m * Mn) := by
    zify at h hUn hUm hM hn0 hnm ⊢
    have e1 : (Un : ℤ) = n - Mn := by linarith
    have e2 : (Um : ℤ) = m - Mm := by linarith
    rw [e1, e2] at h
    nlinarith [h, mul_pos (mul_pos (show (0:ℤ) < Mn by linarith) (show (0:ℤ) < Mn by linarith))
      (show (0:ℤ) < m by linarith)]
  exact Nat.lt_of_mul_lt_mul_left key

end Submissions.ErdosMultiplesDoublingSquareImplies.Complement
