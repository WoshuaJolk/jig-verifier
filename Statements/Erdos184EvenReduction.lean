import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter SimpleGraph

namespace Statements.Erdos184EvenReduction

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
abbrev Root : Prop :=
  ∃ f : ℕ → ℝ,
    (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)



universe u
open scoped Classical

def EvenBound (C : ℝ) : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (∀ v, Even (G.degree v)) →
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ (D.card : ℝ) ≤ C * (Fintype.card V : ℝ)


/-- Conditional reduction; the uniform even-degree bound remains an assumption. -/
abbrev statement : Prop :=
  ∀ C : ℝ, EvenBound.{u} C → Root.{u}

end Statements.Erdos184EvenReduction
