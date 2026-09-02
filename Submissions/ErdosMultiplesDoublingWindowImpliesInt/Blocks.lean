import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Window Bound ⇒ Erdős #488 at integer ratios `m = j n`, `j ≥ 2`.

`[1, (i+1)n] = [1, in] ⊔ (in, (i+1)n]`, so `M((i+1)n) = M(in) + #(B ∩ (in, (i+1)n])`; each
window adds at most `2 M(n)`, hence `M(jn) ≤ (2j − 1) M(n)`, and `M(n) ≥ 1` (it contains any
`a ∈ A`) gives `n · M(jn) ≤ n (2j − 1) M(n) < 2 jn · M(n)`.
-/

namespace Submissions.ErdosMultiplesDoublingWindowImpliesInt.Blocks

open Finset

lemma Icc_split (x n : ℕ) : Icc 1 (x + n) = Icc 1 x ∪ Icc (x + 1) (x + n) := by
  ext k
  simp only [mem_Icc, mem_union]
  omega

lemma Icc_disj (x n : ℕ) : Disjoint (Icc 1 x) (Icc (x + 1) (x + n)) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [mem_Icc] at hk hk'
  omega

lemma card_split (P : ℕ → Prop) [DecidablePred P] (x n : ℕ) :
    ((Icc 1 (x + n)).filter P).card =
      ((Icc 1 x).filter P).card + ((Icc (x + 1) (x + n)).filter P).card := by
  rw [Icc_split x n, filter_union, card_union_of_disjoint]
  exact disjoint_filter_filter (Icc_disj x n)

/-- `M(in) ≤ (2i − 1) M(n)` for `i ≥ 1`, given the window bound for `A, n`. -/
lemma blocks (A : Finset ℕ) (n : ℕ)
    (WB : ∀ x : ℕ, ((Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤
        2 * ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) :
    ∀ i : ℕ, 1 ≤ i →
      ((Icc 1 (i * n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤
        (2 * i - 1) * ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro i hi
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · have h1 := ih h
      have h2 := WB (i * n)
      have h3 := card_split (fun k => ∃ a ∈ A, a ∣ k) (i * n) n
      have h4 : (i + 1) * n = i * n + n := by ring
      have h5 : 2 * (i + 1) - 1 = (2 * i - 1) + 2 := by omega
      rw [h4, h3, h5, add_mul]
      exact Nat.add_le_add h1 h2

theorem proof :
    (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n x : ℕ, (∀ a ∈ A, a ≤ n) →
        ((Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤
          2 * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) →
    ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n j : ℕ, (∀ a ∈ A, a ≤ n) → 2 ≤ j →
        n * ((Finset.Icc 1 (j * n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
          2 * (j * n) * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro WB A hA h0 n j hn hj
  have hb := blocks A n (fun x => WB A hA h0 n x hn) j (by omega)
  obtain ⟨a, ha⟩ := hA
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
  have hM : 1 ≤ ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
    apply Finset.card_pos.mpr
    exact ⟨a, by
      rw [mem_filter, mem_Icc]
      exact ⟨⟨ha0, hn a ha⟩, a, ha, dvd_refl a⟩⟩
  have hn0 : 0 < n := lt_of_lt_of_le ha0 (hn a ha)
  set M := ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card with hMdef
  have h6 : n * ((Icc 1 (j * n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤ n * ((2 * j - 1) * M) :=
    Nat.mul_le_mul_left n hb
  have h7 : n * ((2 * j - 1) * M) < 2 * (j * n) * M := by
    have h8 : (2 * j - 1) + 1 = 2 * j := by omega
    have heq : n * ((2 * j - 1) * M) + n * M = 2 * (j * n) * M := by
      calc n * ((2 * j - 1) * M) + n * M = n * (((2 * j - 1) + 1) * M) := by ring
        _ = 2 * (j * n) * M := by rw [h8]; ring
    have hpos : 0 < n * M := Nat.mul_pos hn0 hM
    omega
  exact lt_of_le_of_lt h6 h7

end Submissions.ErdosMultiplesDoublingWindowImpliesInt.Blocks
