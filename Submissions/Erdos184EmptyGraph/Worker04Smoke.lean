import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph

open SimpleGraph

namespace Submissions.Erdos184EmptyGraph.Worker04Smoke

def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

open scoped Classical in
theorem proof :
    ∃ D : Finset (⊥ : SimpleGraph (Fin 1)).Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition (⊥ : SimpleGraph (Fin 1)) D ∧
      D.card = 0 := by
  refine ⟨∅, by simp, ?_, by simp⟩
  simp [IsDecomposition]

end Submissions.Erdos184EmptyGraph.Worker04Smoke
