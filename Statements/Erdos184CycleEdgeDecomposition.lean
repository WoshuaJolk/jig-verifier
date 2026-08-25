import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter SimpleGraph

namespace Statements.Erdos184CycleEdgeDecomposition

/-- A finite graph is one connected cycle or one edge. -/
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

/-- `D` partitions the edge set of `G` into subgraphs. -/
def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

open scoped Classical in
/-- The Erdős–Gallai cycle decomposition conjecture. -/
abbrev statement : Prop :=
  ∃ f : ℕ → ℝ,
    (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)

 theorem target : statement := sorry

end Statements.Erdos184CycleEdgeDecomposition
