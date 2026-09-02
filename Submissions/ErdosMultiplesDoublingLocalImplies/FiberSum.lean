import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Action.Defs

/-!
Local Doubling ⇒ Erdős #488.

Given `f` with every image in `B ∩ [1, n]` and every fiber of size `< 2m/n` (in the form
`n · #fiber < 2m`), `#(B ∩ [1,m]) = ∑_{d ∈ B ∩ [1,n]} #fiber(d)`, and multiplying by `n` and
summing the strict fiber bounds over the nonempty `B ∩ [1, n]` gives `n · M(m) < 2m · M(n)`.
-/

namespace Submissions.ErdosMultiplesDoublingLocalImplies.FiberSum

open Finset

theorem proof :
    (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        ∃ f : ℕ → ℕ,
          (∀ k ∈ (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k),
            ∃ a ∈ A, ∃ s : ℕ, a ∣ k ∧ f k = a * s ∧ 1 ≤ s ∧ a * s ≤ n ∧
              s * m ≤ (k / a) * n + m ∧ (k / a) * n ≤ s * m + m) ∧
          (∀ d : ℕ,
            n * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
              (fun k => f k = d)).card < 2 * m)) →
    ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
          2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro LD A hA h0 n m hn hnm
  obtain ⟨f, hf, hfib⟩ := LD A hA h0 n m hn hnm
  set P : ℕ → Prop := fun k => ∃ a ∈ A, a ∣ k with hP
  set Bm := (Icc 1 m).filter P with hBm
  set Bn := (Icc 1 n).filter P with hBn
  -- every image lands in Bn
  have himg : ∀ k ∈ Bm, f k ∈ Bn := by
    intro k hk
    obtain ⟨a, ha, s, hak, hfk, hs1, hsn, -, -⟩ := hf k hk
    have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
    rw [hBn, mem_filter, mem_Icc, hfk]
    refine ⟨⟨Nat.mul_pos ha0 hs1, hsn⟩, a, ha, dvd_mul_right a s⟩
  -- fiber decomposition
  have hsum : Bm.card = ∑ d ∈ Bn, (Bm.filter (fun k => f k = d)).card := by
    rw [card_eq_sum_card_fiberwise himg]
  -- Bn nonempty
  have hne : Bn.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
    exact ⟨a, by
      rw [hBn, mem_filter, mem_Icc]
      exact ⟨⟨ha0, hn a ha⟩, a, ha, dvd_refl a⟩⟩
  calc n * Bm.card = ∑ d ∈ Bn, n * (Bm.filter (fun k => f k = d)).card := by
        rw [hsum, Finset.mul_sum]
    _ < ∑ _d ∈ Bn, 2 * m := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro d _
        exact hfib d
    _ = 2 * m * Bn.card := by
        rw [sum_const]
        simp only [smul_eq_mul]
        ring

end Submissions.ErdosMultiplesDoublingLocalImplies.FiberSum
