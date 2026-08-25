import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos74AlmostBipartite

open Filter SimpleGraph
open scoped Topology

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

/-- Erdős Problem 74: arbitrarily slow divergent edge-deletion bounds
are compatible with infinite chromatic number. -/
abbrev statement : Prop :=
  ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    ∃ (V : Type u) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ ∧
      ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n

theorem target : statement := sorry

end Statements.Erdos74AlmostBipartite
