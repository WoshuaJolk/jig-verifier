import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
Harmonic Bound ⇒ Square Bound ∧ Erdős #488.

With `M = M(x)`, `U = x − M`: the hypothesis `M(m)(n + M(n)) ≤ 2m M(n)` gives

* #488: `n M(m) ≤ M(m)(n + M(n)) − M(m) M(n) ≤ 2m M(n) − 1 < 2m M(n)` as `M(m) M(n) ≥ 1`;
* Square: writing `Un = n − M(n)`, `Um = m − M(m)`, the hypothesis is
  `(m − Um)(2n − Un) ≤ 2m(n − Un)`, i.e. `m Un ≤ Um (2n − Un)`; multiply by `Un ≥ 0` and use
  `Un (2n − Un) ≤ n²` (i.e. `(n − Un)² ≥ 0`) to get `m Un² ≤ Um · Un (2n − Un) ≤ Um n²`.
-/

namespace Submissions.ErdosMultiplesDoublingHarmonicImplies.Hierarchy

open Finset

lemma compl_add (A : Finset ℕ) (x : ℕ) :
    ((Icc 1 x).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card +
      ((Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card = x := by
  rw [add_comm, Finset.card_filter_add_card_filter_not, Nat.card_Icc]
  omega

lemma M_pos (A : Finset ℕ) (hA : A.Nonempty) (h0 : 0 ∉ A) (n : ℕ) (hAn : ∀ a ∈ A, a ≤ n) :
    1 ≤ ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  obtain ⟨a, ha⟩ := hA
  apply Finset.card_pos.mpr
  refine ⟨a, ?_⟩
  rw [mem_filter, mem_Icc]
  exact ⟨⟨Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha)), hAn a ha⟩, a, ha, dvd_refl a⟩

lemma M_mono (A : Finset ℕ) {n m : ℕ} (h : n ≤ m) :
    ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤
      ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card :=
  card_le_card (filter_subset_filter _ (Icc_subset_Icc_right h))

theorem proof :
    (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card *
            (n + ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) ≤
          2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) →
    (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * m ≤
          ((Finset.Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card * n ^ 2) ∧
    (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
          2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) := by
  intro H
  constructor
  · intro A hA h0 n m hAn hnm
    have h := H A hA h0 n m hAn hnm
    have hn := compl_add A n
    have hm := compl_add A m
    set Un := ((Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card
    set Um := ((Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card
    set Mn := ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card
    set Mm := ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card
    zify at h hn hm ⊢
    have hUn : (0 : ℤ) ≤ Un := by positivity
    have hUm : (0 : ℤ) ≤ Um := by positivity
    have h1 : (m : ℤ) * Un ≤ Um * (2 * n - Un) := by nlinarith
    have h2 : (Un : ℤ) * (2 * n - Un) ≤ (n : ℤ) ^ 2 := by nlinarith [sq_nonneg ((n : ℤ) - Un)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hUn, mul_le_mul_of_nonneg_left h2 hUm]
  · intro A hA h0 n m hAn hnm
    have h := H A hA h0 n m hAn hnm
    have h1 := M_pos A hA h0 n hAn
    have h2 := M_mono A (le_of_lt hnm)
    set Mn := ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card
    set Mm := ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card
    nlinarith

end Submissions.ErdosMultiplesDoublingHarmonicImplies.Hierarchy
