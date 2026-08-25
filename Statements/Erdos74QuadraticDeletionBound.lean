import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

namespace Statements.Erdos74QuadraticDeletionBound

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

/-- The universal delete-all-edges bound for every finite subgraph size. -/
abbrev statement : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) (n : ℕ),
    maxSubgraphEdgeDistToBipartite G n ≤ n.choose 2

theorem target : statement := sorry

end Statements.Erdos74QuadraticDeletionBound
