import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

open SimpleGraph

namespace Submissions.Erdos23CycleFiveHom.Main

private theorem small_pair (a : Fin 5 → ℕ) (n : ℕ)
    (hs : ∑ i, a i = 5 * n) : ∃ i, a i + a (i + 1) ≤ 2 * n := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  change 2 * n < a 0 + a 1 at h0
  change 2 * n < a 1 + a 2 at h1
  change 2 * n < a 2 + a 3 at h2
  change 2 * n < a 3 + a 4 at h3
  change 2 * n < a 4 + a 0 at h4
  norm_num [Fin.sum_univ_succ] at hs
  change a 0 + (a 1 + (a 2 + (a 3 + a 4))) = 5 * n at hs
  omega

private theorem pair_product (a b n : ℕ) (h : a + b ≤ 2 * n) : a * b ≤ n ^ 2 := by
  have hsq := Nat.pow_le_pow_left h 2
  zify at hsq ⊢
  nlinarith [sq_nonneg ((a : ℤ) - b)]

private def side (i a : Fin 5) : Prop := a = i + 2 ∨ a = i + 4

private theorem cut_table : ∀ i a b : Fin 5,
    (a + 1 = b ∨ b + 1 = a) →
    ¬ ((side i a ∧ ¬ side i b) ∨ (¬ side i a ∧ side i b)) →
    (a = i ∧ b = i + 1) ∨ (a = i + 1 ∧ b = i) := by
  unfold side
  decide

open scoped Classical in
theorem proof :
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ G : SimpleGraph V,
        (∃ c : V → Fin 5, ∀ v w, G.Adj v w → c v + 1 = c w ∨ c w + 1 = c v) →
        ∃ H : SimpleGraph V,
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2 := by
  intro n V _ hcard G ⟨c, hc⟩
  classical
  let fiber (i : Fin 5) : Finset V := Finset.univ.filter (fun v => c v = i)
  have hsum : ∑ i, (fiber i).card = 5 * n := by
    rw [← hcard]
    exact (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := c) (by simp)).symm
  obtain ⟨i, hi⟩ := small_pair (fun i => (fiber i).card) n hsum
  let S := fiber i
  let T := fiber (i + 1)
  let U : Set V := {v | side i (c v)}
  let H := G.between U Uᶜ
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  let R := G \ H
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  have hR : R.IsBipartiteWith (S : Set V) (T : Set V) := by
    constructor
    · rw [Set.disjoint_left]
      intro v hv hw
      have hv' : c v = i := by simpa [S, fiber] using hv
      have hw' : c v = i + 1 := by simpa [T, fiber] using hw
      have hne : ∀ j : Fin 5, j ≠ j + 1 := by decide
      exact hne i (hv'.symm.trans hw')
    · intro v w hvw
      have hrel := hc v w hvw.1
      have hsame : ¬ ((side i (c v) ∧ ¬ side i (c w)) ∨
          (¬ side i (c v) ∧ side i (c w))) := by
        intro h
        exact hvw.2 ⟨hvw.1, h⟩
      simpa [S, T, fiber] using cut_table i (c v) (c w) hrel hsame
  have hcount : R.edgeFinset.card ≤ S.card * T.card := by
    have heq : R.edgeFinset.card = ∑ v ∈ S, R.degree v := by
      simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using
        (isBipartiteWith_sum_degrees_eq_card_edges hR).symm
    rw [heq]
    calc
      ∑ v ∈ S, R.degree v ≤ ∑ _v ∈ S, T.card := by
        apply Finset.sum_le_sum
        intro v hv
        rw [← card_neighborFinset_eq_degree]
        apply Finset.card_le_card
        intro w hw
        exact hR.mem_of_mem_adj hv (by simpa using hw)
      _ = S.card * T.card := by simp
  refine ⟨H, G.between_le, G.between_isBipartite disjoint_compl_right, ?_⟩
  calc
    (G.edgeFinset \ H.edgeFinset).card = R.edgeFinset.card := by
      simp [R]
    _ ≤ S.card * T.card := hcount
    _ ≤ n ^ 2 := pair_product _ _ n hi

end Submissions.Erdos23CycleFiveHom.Main
