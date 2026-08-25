import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

namespace Statements.Erdos74DeletionWitness

open SimpleGraph

universe u

def edgeDistancesToBipartite {V : Type u} {G : SimpleGraph V}
    (A : G.Subgraph) : Set ℕ :=
  {k | ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧
    IsBipartite (A.deleteEdges E).coe ∧ k = E.ncard}

/-- Deleting every edge witnesses that the edge-distance set is nonempty. -/
abbrev statement : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) (A : G.Subgraph),
    (edgeDistancesToBipartite A).Nonempty

theorem target : statement := sorry

end Statements.Erdos74DeletionWitness
