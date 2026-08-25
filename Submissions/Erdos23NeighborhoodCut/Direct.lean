import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Submissions.Erdos23NeighborhoodCut.Direct

open scoped Classical in
theorem proof :
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        (∃ v : V,
          G.edgeFinset.card ≤
            n ^ 2 + ∑ w ∈ G.neighborFinset v, G.degree w) →
          ∃ (H : SimpleGraph V),
            H ≤ G ∧ H.IsBipartite ∧
              (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2 := by
  intro n V _ _ G htri ⟨v, hv⟩
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
    simp [H, SimpleGraph.between_adj, hx, hyout]
    exact hyout
  have hcard : H.edgeFinset.card = ∑ x ∈ s, G.degree x := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hbwith]
    exact Finset.sum_congr rfl fun x hx ↦ hdeg x hx
  refine ⟨H, hle, hbip, ?_⟩
  calc
    (G.edgeFinset \ H.edgeFinset).card =
        G.edgeFinset.card - H.edgeFinset.card :=
      Finset.card_sdiff_of_subset (edgeFinset_mono hle)
    _ = G.edgeFinset.card - ∑ x ∈ s, G.degree x := by rw [hcard]
    _ ≤ n ^ 2 := by
      change G.edgeFinset.card ≤ n ^ 2 + ∑ w ∈ s, G.degree w at hv
      omega

end Submissions.Erdos23NeighborhoodCut.Direct
