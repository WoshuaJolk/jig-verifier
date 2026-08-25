import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

open SimpleGraph

namespace Statements.Erdos184SingletonEdgeDecomposition

def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

open scoped Classical in
/-- Every finite graph decomposes into one-edge subgraphs, using at most one piece per edge. -/
abbrev statement : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧
      D.card ≤ G.edgeFinset.card

theorem target : statement := sorry

end Statements.Erdos184SingletonEdgeDecomposition
