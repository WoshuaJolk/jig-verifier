import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

namespace Submissions.Erdos74QuadraticDeletionBound.Universal

open SimpleGraph

universe u

def edgeDistancesToBipartite {V : Type u} {G : SimpleGraph V}
    (A : G.Subgraph) : Set ℕ :=
  {k | ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧
    IsBipartite (A.deleteEdges E).coe ∧ k = E.ncard}

noncomputable def minEdgeDistToBipartite {V : Type u} {G : SimpleGraph V}
    (A : G.Subgraph) : ℕ :=
  sInf (edgeDistancesToBipartite A)

def subgraphEdgeDistsToBipartite {V : Type u}
    (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  {k | ∃ A : G.Subgraph, A.verts.ncard = n ∧ A.verts.Finite ∧
    k = minEdgeDistToBipartite A}

noncomputable def maxSubgraphEdgeDistToBipartite {V : Type u}
    (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup (subgraphEdgeDistsToBipartite G n)

theorem proof : ∀ (V : Type u) (G : SimpleGraph V) (n : ℕ),
    maxSubgraphEdgeDistToBipartite G n ≤ n.choose 2 := by
  intro V G n
  apply csSup_le'
  intro m hm
  rcases hm with ⟨A, hn, hfin, rfl⟩
  have hedge : A.edgeSet.ncard ≤ n.choose 2 := by
    rw [← hn]
    letI := hfin.fintype
    letI := Fintype.ofFinite ↑A.coe.edgeSet
    convert (A.coe).card_edgeFinset_le_card_choose_two
    · rw [← Set.ncard_coe_finset A.coe.edgeFinset, coe_edgeFinset A.coe,
        ← Subgraph.image_coe_edgeSet_coe A]
      exact (Set.ncard_image_iff (Set.toFinite A.coe.edgeSet)).mpr
        (Function.Injective.injOn (Sym2.map.injective Subtype.coe_injective))
    · rw [Set.ncard_eq_toFinset_card _ hfin, Set.Finite.card_toFinset]
  refine le_trans (Nat.sInf_le ?_) hedge
  exact ⟨A.edgeSet, fun _ h => h, ⟨fun _ => 0, by
    intro v w h
    change (A.deleteEdges A.edgeSet).Adj v.1 w.1 at h
    rw [Subgraph.deleteEdges_adj] at h
    exact (h.2 h.1).elim⟩, rfl⟩

end Submissions.Erdos74QuadraticDeletionBound.Universal
