import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

namespace Submissions.Erdos74DeletionWitness.Direct

open SimpleGraph

universe u

def edgeDistancesToBipartite {V : Type u} {G : SimpleGraph V}
    (A : G.Subgraph) : Set ℕ :=
  {k | ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧
    IsBipartite (A.deleteEdges E).coe ∧ k = E.ncard}

theorem proof : ∀ (V : Type u) (G : SimpleGraph V) (A : G.Subgraph),
    (edgeDistancesToBipartite A).Nonempty := by
  intro V G A
  refine ⟨A.edgeSet.ncard, A.edgeSet, fun _ h => h, ?_, rfl⟩
  refine ⟨fun _ => 0, ?_⟩
  intro v w h
  change (A.deleteEdges A.edgeSet).Adj v.1 w.1 at h
  rw [Subgraph.deleteEdges_adj] at h
  exact (h.2 h.1).elim

end Submissions.Erdos74DeletionWitness.Direct
