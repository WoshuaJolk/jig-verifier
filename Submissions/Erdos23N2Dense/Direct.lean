import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23N2Dense.Direct

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
lemma dense_neighborhood_ineq
    (V : Type) [Fintype V] (hcard : Fintype.card V = 10)
    (G : SimpleGraph V) (hdense : 18 ≤ G.edgeFinset.card) :
    ∃ v : V,
      G.edgeFinset.card ≤
        4 + ∑ w ∈ G.neighborFinset v, G.degree w := by
  classical
  let m := G.edgeFinset.card
  by_contra! hnone
  have hm18 : 18 ≤ m := by simpa [m] using hdense
  have hpoint :
      ∀ v : V, (∑ w ∈ G.neighborFinset v, G.degree w) ≤ m - 5 := by
    intro v
    have hv := hnone v
    change 4 + (∑ w ∈ G.neighborFinset v, G.degree w) < m at hv
    omega
  have hsum :
      (∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree w) ≤
        10 * (m - 5) := by
    calc
      _ ≤ ∑ _v : V, (m - 5) := Finset.sum_le_sum fun _ _ ↦ hpoint _
      _ = 10 * (m - 5) := by simp [hcard]
  have hsq :
      (∑ v : V, G.degree v) ^ 2 ≤
        10 * ∑ v : V, (G.degree v) ^ 2 := by
    simpa [hcard] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun v : V ↦ G.degree v))
  have hhand : ∑ v : V, G.degree v = 2 * m := by
    simpa [m] using G.sum_degrees_eq_twice_card_edges
  have hquad :
      7 * (∑ v : V, G.degree v) ≤
        (∑ v : V, (G.degree v) ^ 2) + 120 := by
    have hpoint_quad : ∀ v : V, 7 * G.degree v ≤ (G.degree v) ^ 2 + 12 := by
      intro v
      have hdeg : G.degree v ≤ 9 := by
        have := G.degree_lt_card_verts v
        omega
      interval_cases G.degree v <;> norm_num
    calc
      7 * (∑ v : V, G.degree v) =
          ∑ v : V, 7 * G.degree v := by rw [Finset.mul_sum]
      _ ≤ ∑ v : V, ((G.degree v) ^ 2 + 12) :=
        Finset.sum_le_sum fun v _ ↦ hpoint_quad v
      _ = (∑ v : V, (G.degree v) ^ 2) + 120 := by
        simp [Finset.sum_add_distrib, hcard]
  rw [sum_neighbor_degrees_eq_sum_sq G] at hsum
  rw [hhand] at hsq
  have hcomb : (2 * m) ^ 2 ≤ 100 * (m - 5) := by
    calc
      (2 * m) ^ 2 ≤ 10 * ∑ v : V, (G.degree v) ^ 2 := hsq
      _ ≤ 10 * (10 * (m - 5)) := Nat.mul_le_mul_left 10 hsum
      _ = 100 * (m - 5) := by ring
  have hm45 : m ≤ Nat.choose 10 2 := by
    simpa [m, hcard] using G.card_edgeFinset_le_card_choose_two
  norm_num [Nat.choose] at hm45
  by_cases heq : m = 18
  · subst m
    omega
  · have hm19 : 19 ≤ m := by omega
    interval_cases m <;> norm_num at hcomb

open scoped Classical in
theorem proof :
    ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        18 ≤ G.edgeFinset.card →
          ∃ (H : SimpleGraph V),
            H ≤ G ∧ H.IsBipartite ∧
              (G.edgeFinset \ H.edgeFinset).card ≤ 4 := by
  intro V _ hcard G htri hdense
  obtain ⟨v, hv⟩ := dense_neighborhood_ineq V hcard G hdense
  let S : Finset V := G.neighborFinset v
  let H : SimpleGraph V := G.between (↑S : Set V) ↑(Sᶜ)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hind : G.IsIndepSet (↑S : Set V) := by
    simpa [S, neighborFinset_def] using
      G.isIndepSet_neighborSet_of_triangleFree htri v
  have hle : H ≤ G := G.between_le
  have hd : Disjoint (↑S : Set V) ↑(Sᶜ) := by
    rw [Finset.coe_compl]
    exact disjoint_compl_right
  have hbwith : H.IsBipartiteWith (↑S : Set V) ↑(Sᶜ) := by
    simpa [H] using
      (G.between_isBipartiteWith
        (s := (↑S : Set V)) (t := (↑(Sᶜ) : Set V)) hd)
  have hbip : H.IsBipartite := hbwith.isBipartite
  have hdeg : ∀ x ∈ S, H.degree x = G.degree x := by
    intro x hx
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    congr 1
    ext y
    have hyout : G.Adj x y → y ∉ S := by
      intro hxy hy
      exact hind hx hy (G.ne_of_adj hxy) hxy
    simp [H, SimpleGraph.between_adj, hx]
    exact hyout
  have hedge : H.edgeFinset.card = ∑ x ∈ S, G.degree x := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hbwith]
    exact Finset.sum_congr rfl fun x hx ↦ hdeg x hx
  refine ⟨H, hle, hbip, ?_⟩
  calc
    (G.edgeFinset \ H.edgeFinset).card =
        G.edgeFinset.card - H.edgeFinset.card :=
      Finset.card_sdiff_of_subset (edgeFinset_mono hle)
    _ = G.edgeFinset.card - ∑ x ∈ S, G.degree x := by rw [hedge]
    _ ≤ 4 := by
      change G.edgeFinset.card ≤ 4 + ∑ w ∈ S, G.degree w at hv
      omega

end Submissions.Erdos23N2Dense.Direct
