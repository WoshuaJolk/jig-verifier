import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23N1Case.Direct

open scoped Classical in
lemma sum_neighbor_degrees_eq_sum_sq
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    (∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree w) =
      ∑ w : V, (G.degree w) ^ 2 := by
  classical
  calc
    (∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree w) =
        ∑ v : V, ∑ w : V, if G.Adj v w then G.degree w else 0 := by
      simp [neighborFinset_eq_filter, Finset.sum_filter]
    _ = ∑ w : V, ∑ v : V, if G.Adj v w then G.degree w else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ w : V, G.degree w * G.degree w := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_filter]
      simp [← G.card_neighborFinset_eq_degree, neighborFinset_eq_filter, G.adj_comm]
    _ = ∑ w : V, (G.degree w) ^ 2 := by
      simp [pow_two]

open scoped Classical in
lemma neighborhood_ineq
    (V : Type) [Fintype V] (hcard : Fintype.card V = 5)
    (G : SimpleGraph V) :
    ∃ v : V,
      G.edgeFinset.card ≤
        1 + ∑ w ∈ G.neighborFinset v, G.degree w := by
  classical
  let m := G.edgeFinset.card
  by_cases hm : m ≤ 1
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact ⟨Classical.choice inferInstance, by omega⟩
  · by_contra! hnone
    have hm2 : 2 ≤ m := by omega
    have hpoint :
        ∀ v : V, (∑ w ∈ G.neighborFinset v, G.degree w) ≤ m - 2 := by
      intro v
      have hv := hnone v
      change 1 + (∑ w ∈ G.neighborFinset v, G.degree w) < m at hv
      omega
    have hsum :
        (∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree w) ≤
          5 * (m - 2) := by
      calc
        _ ≤ ∑ _v : V, (m - 2) := Finset.sum_le_sum fun _ _ ↦ hpoint _
        _ = 5 * (m - 2) := by simp [hcard]
    have hsq :
        (∑ v : V, G.degree v) ^ 2 ≤
          5 * ∑ v : V, (G.degree v) ^ 2 := by
      simpa [hcard] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun v : V ↦ G.degree v))
    have hhand : ∑ v : V, G.degree v = 2 * m := by
      simpa [m] using G.sum_degrees_eq_twice_card_edges
    rw [sum_neighbor_degrees_eq_sum_sq G] at hsum
    rw [hhand] at hsq
    have hcomb : (2 * m) ^ 2 ≤ 25 * (m - 2) := by
      calc
        (2 * m) ^ 2 ≤ 5 * ∑ v : V, (G.degree v) ^ 2 := hsq
        _ ≤ 5 * (5 * (m - 2)) := Nat.mul_le_mul_left 5 hsum
        _ = 25 * (m - 2) := by ring
    have hm10 : m ≤ Nat.choose 5 2 := by
      simpa [m, hcard] using G.card_edgeFinset_le_card_choose_two
    norm_num [Nat.choose] at hm10
    interval_cases m <;> norm_num at hcomb

open scoped Classical in
theorem proof :
    ∀ (V : Type) [Fintype V], Fintype.card V = 5 →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧
            (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  intro V _ hcard G htri
  obtain ⟨v, hv⟩ := neighborhood_ineq V hcard G
  let s : Finset V := G.neighborFinset v
  let H : SimpleGraph V := G.between (↑s : Set V) ↑(sᶜ)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hind : G.IsIndepSet (↑s : Set V) := by
    simpa [s, neighborFinset_def] using
      G.isIndepSet_neighborSet_of_triangleFree htri v
  have hle : H ≤ G := G.between_le
  have hd : Disjoint (↑s : Set V) ↑(sᶜ) := by
    rw [Finset.coe_compl]
    exact disjoint_compl_right
  have hbwith : H.IsBipartiteWith (↑s : Set V) ↑(sᶜ) := by
    simpa [H] using
      (G.between_isBipartiteWith
        (s := (↑s : Set V)) (t := (↑(sᶜ) : Set V)) hd)
  have hbip : H.IsBipartite := hbwith.isBipartite
  have hdeg : ∀ x ∈ s, H.degree x = G.degree x := by
    intro x hx
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    congr 1
    ext y
    have hyout : G.Adj x y → y ∉ s := by
      intro hxy hy
      exact hind hx hy (G.ne_of_adj hxy) hxy
    simp [H, SimpleGraph.between_adj, hx]
    exact hyout
  have hedge : H.edgeFinset.card = ∑ x ∈ s, G.degree x := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hbwith]
    exact Finset.sum_congr rfl fun x hx ↦ hdeg x hx
  refine ⟨H, hle, hbip, ?_⟩
  calc
    (G.edgeFinset \ H.edgeFinset).card =
        G.edgeFinset.card - H.edgeFinset.card :=
      Finset.card_sdiff_of_subset (edgeFinset_mono hle)
    _ = G.edgeFinset.card - ∑ x ∈ s, G.degree x := by rw [hedge]
    _ ≤ 1 := by
      change G.edgeFinset.card ≤ 1 + ∑ w ∈ s, G.degree w at hv
      omega

end Submissions.Erdos23N1Case.Direct
